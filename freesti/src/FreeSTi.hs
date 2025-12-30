module FreeSTi where

import Control.Monad.Except (runExceptT)
import Control.Monad.State ( runState, foldM, forM_ )
import Control.Monad.Trans (lift)
import Data.Char ( isSpace )
import Data.List ( break, isPrefixOf )
import Data.Map qualified as Map
import Options.Applicative ( execParser )
import System.Console.Haskeline
import System.Exit (die)

import CLI ( RunOpts, opts )
import FreeST (preludePath)
import Parser.LexerUtils
import Parser.Parser
import Parser.Scoping qualified as Scoping
import Parser.Unparser
import Paths_freest (getDataFileName)
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Expression qualified as E
import UI.Error (Error, showErrors, Source)
import Validation.Base
import Validation.Kinding qualified as Kinding
import Validation.Normalisation (normalise)
import Validation.TypeEquivalence (equivalent)
import Validation.Typing qualified as Typing

main :: IO ()
main = execParser opts >>= freesti

data REPLState = REPLState
  { src             :: Source
  , replModule      :: M.Module
  , scopingState    :: Scoping.ScopingState
  , scopingCtx      :: Scoping.ScopingCtx
  , validationState :: ValidationState
  , typeCtx         :: Typing.TypeCtx
  , kindCtx         :: Kinding.KindCtx
  }

emptyREPLState :: REPLState
emptyREPLState = REPLState
  { src             = Map.empty
  , replModule      = M.empty
  , scopingState    = Scoping.emptyScopingState
  , scopingCtx      = Scoping.emptyScopingCtx
  , validationState = emptyValidationState
  , typeCtx         = Typing.emptyTypeCtx
  , kindCtx         = Kinding.emptyKindCtx
  }

interactivePath :: Int -> String
interactivePath i = "<input " ++ show i ++ ">"

freesti :: RunOpts -> IO ()
freesti opts = do
  preludeSrc <- getDataFileName preludePath >>= readFile
  let s = emptyREPLState{src = Map.fromList [(preludePath, lines preludeSrc)]}
  runInputT defaultSettings
    case runParseModule preludePath preludeSrc
         >>= runScopeModule (scopingState s) (scopingCtx s) of
      Left es -> outputErrors 1 s es
      Right (m, scopingCtx, scopingState) ->
        case runValidateModule (typeCtx s) m of
          Left es -> outputErrors 1 s es
          Right (replModule, typeCtx, validationState) ->
            repl 1 s{replModule, scopingState, scopingCtx, validationState, typeCtx}

repl :: Int -> REPLState -> InputT IO ()
repl i s = do
  minput <- getInputLine "freesti> "
  case minput of
    Nothing -> lift $ die "Leaving FreeSTi."
    Just (dropWhile isSpace -> ':' : (break isSpace -> (cmd, val))) ->
      if null cmd
        then outputStrLn "Incomplete command `:`" >> repl (i + 1) s
        else do
          let src' = Map.insert (interactivePath i) (lines val) (src s)
          handleCommand i s{src=src'} cmd val
    Just input -> do outputStrLn "Cannot evaluate input yet..."
                     repl (i + 1) s

outputErrors :: Int -> REPLState -> [Error] -> InputT IO ()
outputErrors i s es = (outputStrLn . showErrors (src s)) es >> repl (i + 1) s

commands :: Map.Map String (Int -> REPLState -> String -> InputT IO ())
commands = Map.fromList
  [ ("equivalent", handleEquivalent)
  , ("kind"      , handleKind)
  , ("normalise" , handleNormalise)
  , ("quit"      , handleQuit)
  , ("type"      , handleType)
  ]
  where
    handleEquivalent :: Int -> REPLState -> String -> InputT IO ()
    handleEquivalent i s src =
      case do
        runLexer parseTypePrimaryListWS (interactivePath i) src
        >>= foldM (\(ts, ctx, ss) t -> do
            (t, ctx', ss') <- runScopeType ss ctx t
            return (t : ts, ctx', ss'))
          ([], scopingCtx s, scopingState s)
      of Left es -> outputErrors i s es
         Right (ts, scopingCtx, scopingState) ->
          case do
            runValidation (validationState s)
              (forM_ ts (Kinding.synth (kindCtx s)))
          of Left es -> outputErrors i s es
             Right _ -> do
              outputStrLn $ show $ 
                all (uncurry $ equivalent $ validationState s)
                  [(t,u) | t <- ts, u <- ts]
              repl (i + 1) s{scopingState, scopingCtx}  

    handleKind :: Int -> REPLState -> String -> InputT IO ()
    handleKind i s src =
      case do
        runLexer parseType (interactivePath i) src
        >>= runScopeType (scopingState s) (scopingCtx s)
      of Left es -> outputErrors i s es
         Right (t, scopingCtx, scopingState) ->
          case runValidation (validationState s)
                 (Kinding.synth (kindCtx s) t)
          of Left es -> outputErrors i s es
             Right k -> do
              outputStrLn (src ++ " : " ++ unparse k)
              repl (i + 1) s{scopingState, scopingCtx}

    handleNormalise :: Int -> REPLState -> String -> InputT IO ()
    handleNormalise i s src =
      case do
        runLexer parseType (interactivePath i) src
        >>= runScopeType (scopingState s) (scopingCtx s)
      of Left es -> outputErrors i s es
         Right (t, scopingCtx, scopingState) ->
          case runValidation (validationState s)
                 (Kinding.synth (kindCtx s) t)
          of Left es -> outputErrors i s es
             Right _ -> do
              outputStrLn (unparse (normalise (validationState s) t))
              repl (i + 1) s{scopingState, scopingCtx}

    handleType :: Int -> REPLState -> String -> InputT IO ()
    handleType i s src =
      case runLexer parseExp (interactivePath i) src
           >>= runScopeExp (scopingState s) (scopingCtx s)
      of Left es -> outputErrors i s es
         Right (e, scopingCtx, scopingState) ->
          case runValidation (validationState s)
                             (Typing.synth Kinding.emptyKindCtx (typeCtx s) e) 
          of Left es -> outputErrors i s es
             Right (t, typeCtx) -> do
              outputStrLn (src ++ " : " ++ unparse t)
              repl (i + 1) s{scopingState, scopingCtx, typeCtx}

    handleQuit :: Int -> REPLState -> String -> InputT IO ()
    handleQuit _ _ _ = lift $ die "Leaving FreeSTi."


handleCommand :: Int -> REPLState -> String -> String -> InputT IO ()
handleCommand i s cmd val =
  case Map.lookupMin (Map.filterWithKey (\k _ -> cmd `isPrefixOf` k) commands) of
    Just (_, handler) -> handler i s val
    Nothing -> outputStrLn ("unknown command `:"++ cmd ++"`") >> repl (i + 1) s

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
  let (em', s') = runState 
        (runExceptT (Kinding.kindModule m >>= Typing.typeModule))
        (buildValidationState m)
  in case em' of
    Left e -> Left (errors s' ++ [e])
    Right (m', tctx) | null (errors s') -> Right (m', tctx, s')
                     | otherwise   -> Left (errors s')
