module FreeSTi where

import Data.Char ( isSpace )
import Data.List ( break, isPrefixOf )
import Data.Map qualified as Map
import System.Console.Haskeline
import Options.Applicative ( execParser )

import Validation.Base
import Parser.Scoping qualified as Scoping
import CLI ( RunOpts, opts )
import Parser.LexerUtils
import Parser.Parser
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Expression qualified as E
import Validation.Kinding qualified as Kinding
import Data.Function ((&))
import UI.Error (Error)
import Validation.Typing qualified as Typing
import Control.Monad.State ( runState )
import Paths_freest (getDataFileName)
import FreeST (preludePath)
import Control.Monad.Except (runExceptT)
import System.Exit (die)
import Control.Monad.Trans (lift)

main :: IO ()
main = execParser opts >>= freesti

data REPLState = REPLState 
  { replModule      :: M.Module 
  , scopingState    :: Scoping.ScopingState
  , scopingCtx      :: Scoping.ScopingCtx
  , validationState :: ValidationState
  , typeCtx         :: Typing.TypeCtx
  }

emptyREPLState :: REPLState
emptyREPLState = REPLState 
  { replModule = M.empty
  , scopingState = Scoping.emptyScopingState
  , scopingCtx = Scoping.emptyScopingCtx
  , validationState = emptyValidationState
  , typeCtx         = Typing.emptyTypeCtx
  }

freesti :: RunOpts -> IO ()
freesti opts = do
  let s = emptyREPLState
  preludeSrc <- getDataFileName preludePath >>= readFile
  runInputT defaultSettings
    case runParseModule preludePath preludeSrc 
         >>= runScopeModule (scopingState s) (scopingCtx s) of 
      Left es -> outputErrors s es
      Right (m, scopingCtx, scopingState) ->
        case runValidateModule (typeCtx s) m of
          Left es -> outputErrors s es
          Right (replModule, typeCtx, validationState) -> 
            repl s{replModule, scopingState, scopingCtx, validationState, typeCtx}

repl :: REPLState -> InputT IO ()
repl s = do
  minput <- getInputLine "freesti> "
  case minput of
    Nothing -> lift $ die "Leaving FreeSTi."
    Just (dropWhile isSpace -> ':' : (break isSpace -> (cmd, val))) ->
      if null cmd 
        then outputStrLn "Incomplete command `:`" >> repl s
        else handleCommand s cmd val
    Just input -> do outputStrLn $ "Input was: " ++ input
                     repl s

outputErrors :: REPLState -> [Error] -> InputT IO ()
outputErrors s es = mapM_ (outputStrLn . show) es >> repl s

commands :: Map.Map String (REPLState -> String -> InputT IO ())
commands = Map.fromList 
  [ ("type", handleType)
  , ("kind", handleKind)
  , ("quit", handleQuit)
  ]
  where
    handleKind :: REPLState -> String -> InputT IO ()
    handleKind s val =
      runLexer parseType "<interactive>" val 
      >>= runScopeType (scopingState s) (scopingCtx s) & \case 
        Left es -> outputErrors s es
        Right (t, scopingCtx, scopingState) -> 
          case runValidation (validationState s) 
                             (Kinding.synth Kinding.emptyKindCtx t) of
          Left es -> outputErrors s es
          Right k -> do 
            outputStrLn (show t ++ " : " ++ show k)
            repl s{scopingState, scopingCtx}
    handleType :: REPLState -> String -> InputT IO ()
    handleType s val = 
      runLexer parseExp "<interactive>" val
      >>= runScopeExp (scopingState s) (scopingCtx s) & \case 
        Left es -> outputErrors s es
        Right (e, scopingCtx, scopingState) -> 
          case runValidation (validationState s) 
                             (Typing.synth Kinding.emptyKindCtx (typeCtx s) e) of 
            Left es -> outputErrors s es
            Right (t, typeCtx) -> do 
              outputStrLn (show e ++ " : " ++ show t)
              repl s{scopingState, scopingCtx, typeCtx}

    handleQuit :: REPLState -> String -> InputT IO ()
    handleQuit _ _ = lift $ die "Leaving FreeSTi."


handleCommand :: REPLState -> String -> String -> InputT IO ()
handleCommand s cmd val =
  case Map.lookupMin (Map.filterWithKey (\k _ -> cmd `isPrefixOf` k) commands) of
    Just (_, handler) -> handler s val
    Nothing -> outputStrLn ("unknown command `:"++ cmd ++"`") >> repl s

runScopeType :: Scoping.ScopingState 
             -> Scoping.ScopingCtx 
             -> T.Type 
             -> Either [Error] (T.Type, Scoping.ScopingCtx, Scoping.ScopingState)
runScopeType s ctx t = 
  let (t', s') = runState (Scoping.scopeType ctx t) s
  in if null (Scoping.errors s') then Right (t', ctx, s') else Left (Scoping.errors s')

runScopeExp :: Scoping.ScopingState 
            -> Scoping.ScopingCtx 
            -> E.Exp 
            -> Either [Error] (E.Exp, Scoping.ScopingCtx, Scoping.ScopingState)
runScopeExp s ctx e = 
  let (e', s') = runState (Scoping.scopeExp ctx e) s
  in if null (Scoping.errors s') then Right (e', ctx, s') else Left (Scoping.errors s')

runScopeModule :: Scoping.ScopingState 
               -> Scoping.ScopingCtx 
               -> M.Module 
               -> Either [Error] (M.Module, Scoping.ScopingCtx, Scoping.ScopingState)
runScopeModule s ctx m = 
  let ((ctx',m'), s') = runState (Scoping.scopeModule' ctx m) s
  in if null (Scoping.errors s') then Right (m', ctx', s') else Left (Scoping.errors s')

runValidateModule :: Typing.TypeCtx 
                  -> M.Module
                  -> Either [Error] (M.Module, Typing.TypeCtx, ValidationState)
runValidateModule tctx m = 
  let (em', s') = runState (runExceptT (Kinding.kindModule m >> Typing.typeModule m)) (buildValidationState m)
  in case em' of
    Left e -> Left (errors s' ++ [e])
    Right (m', tctx) | null (errors s') -> Right (m', tctx, s') 
                     | otherwise   -> Left (errors s')