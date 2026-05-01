module FreeSTi (main) where

import Parser.Lexer (layoutSC)
import Parser.LexerUtils (runLexer, pushStartCode)
import Parser.Parser (parseType, parseTwoTypes, parseTypes, parseCommand)
import Parser.Scoping 
  ( ScopingCtx, emptyScopingCtx, scopeType, freshInternal, insertTId, insertDId)
import Parser.Unparser (unparse)
import Syntax.Base ( Located(spanFromTo) )
import Syntax.Command ( Equation(..), Command(..) )
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import UI.Error (showErrors, Error)
import Validation.Base (Validation, ValidationState (..), emptyValidationState, runValidation)
import Validation.Kinding qualified as Kinding
import Validation.Normalisation (normalise)
import Validation.TypeEquivalence (equivalent, showGrammar, fromTypes)

import Control.Monad.State
import Data.Bitraversable (bimapM)
import Data.List qualified as List
import Data.Map qualified as Map
import System.Console.Repline
import System.Exit (exitSuccess)
import System.Process (callCommand, system)

type Repl a = HaskelineT (StateT ReplState IO) a

data ReplState =
  ReplState { validationState :: ValidationState
            , scopingCtx :: ScopingCtx
            , modl :: M.Module
            }

cmd :: String -> Repl ()
cmd src = do
  s <- get
  case runLexer (pushStartCode layoutSC >> parseCommand) interactivePath (src ++ "\n") of
    Left es -> printErrors src es
    Right c -> case c of
      Type t -> case 
          runValidation (validationState s) $
            scopeType (scopingCtx s) t
            >>= Kinding.synth (modl s) Map.empty of 
        Left es -> printErrors src es
        Right (t', vs) -> do
            unless (null $ errors vs) $ printErrors src (errors vs)
            let t'' = normalise (modl s) t'
            liftIO $ putStrLn (unparse t'' ++ " : " ++ unparse (TK.kindOf t''))
            modify (\s -> s{validationState = vs})
      Equations ds -> do
        let modl' = foldr insertKindSig (modl s) ds
            ctx' = foldr scopeEquation (scopingCtx s) ds
        case runValidation (validationState s) (foldM (insertEquation ctx') modl' ds) of
          Left es -> printErrors src es
          Right (modl'', vs) -> do
            unless (null $ errors vs) $ printErrors src (errors vs)
            modify \s -> s{scopingCtx = ctx', modl = modl''}

insertKindSig :: Equation -> M.Module -> M.Module
insertKindSig (i, map snd -> ks, t, k) m = 
  m{M.kindSigs = Map.insert i (buildArrow ks k) (M.kindSigs m)}
  where buildArrow ks k = foldr (\k k' -> K.Arrow (spanFromTo k k') k k') k ks

scopeEquation :: Equation -> ScopingCtx -> ScopingCtx
scopeEquation (i, _, _, _) = insertTId i

insertEquation :: ScopingCtx -> M.Module -> Equation -> Validation M.Module
insertEquation ctx modl (i, aks, t, k) = do 
  t' <- scopeType ctx (if null aks then t else TU.Abs (spanFromTo i t) aks t)
  t'' <- Kinding.check modl Map.empty t' (M.kindSigs modl Map.! i)
  return modl{M.typeDecls = Map.insert i t'' (M.typeDecls modl)}


interactivePath :: String
interactivePath = "<interactive>"

optPrefix :: Char
optPrefix = ':'

prefixedOpts :: [String]
prefixedOpts = map ((optPrefix :) . fst) opts

-- Prefix tab completeter
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = map (, listCompleter []) prefixedOpts

-- Default tab completer
byWord :: Monad m => WordCompleter m
byWord n = return $ filter (List.isPrefixOf n) prefixedOpts

opts :: [(String, String -> Repl ())]
opts = [ ("?"         , handleHelp)
       , ("help"      , handleHelp)
       , ("kind"      , handleKind)
       , ("equivalent", handleEquivalent)
       , ("normalise" , handleNormalise)
       , ("grammar"   , handleGrammar)
       , ("quit"      , const $ liftIO exitSuccess)
       ]
  where
    handleHelp :: String -> Repl ()
    handleHelp args = liftIO $ putStrLn $ unlines
      [ "Commands available from the prompt:"
      , ind "<type>                        show the normal form and kind of <type>"
      , ind "<typedecl>                    define a type (use :m for mutual recursion)"
      , ind ":kind <type>                  show the kind of <type>"
      , ind ":normalise <type>             show the normal form of <type>"
      , ind ":equivalent <type1> <type2>   check if <type1> is equivalent to <type2>"
      , ind ":grammar <type1> ... <typen>  show the grammar for types <type1> through <typen>"
      , ind ":m                            enter multi-line mode"
      , ind ":?, :help                     display this list of commands"
      , "(for : commands, writing a prefix is enough, e.g., :k <type>)"
      , ""
      , "Type equations need kind information for each parameter and for the right-hand side."
      , "If omitted, kinds default to *T. The syntax is as follows:"
      , ind "<equation> ::= type <upperId> (<lowerId> : <kind>) ... = <type> : <kind>"
      , ""
      , "For : commands, writing a prefix is enough, e.g., :k <type>." 
      , "For commands :equivalent and :grammar, which take multiple arguments, you may need"
      , "to use parenthesis to prevent type-level applications from being parsed as different"
      , "arguments. E.g., :g T U shows the grammar for types T and U while :g (T U) shows the"
      , "grammar for type T applied to U"
      ]
      where ind = ("  " ++)

    handleKind src = do
      s <- get
      case runLexer parseType interactivePath src of
        Left es -> printErrors src es
        Right t -> case runValidation (validationState s) do
            t' <- scopeType (scopingCtx s) t
            Kinding.synth (modl s) Map.empty t'
          of Left es -> do 
              printErrors src es
             Right (t'', vs) -> do
              unless (null $ errors vs) $ printErrors src (errors vs)
              liftIO $ putStrLn (src ++ " : " ++ unparse (TK.kindOf t''))
              modify (\s -> s{validationState = vs})
              
    handleEquivalent src = do
      s <- get
      case runLexer parseTwoTypes interactivePath src of
        Left  es -> printErrors src es
        Right (t, u) -> case runValidation (validationState s) $
            bimapM (scopeType (scopingCtx s) >=> Kinding.synth (modl s) Map.empty)
                   (scopeType (scopingCtx s) >=> Kinding.synth (modl s) Map.empty)
                   (t, u)
          of Left es -> do 
              printErrors src es
             Right ((t', u'), vs) -> do
              unless (null $ errors vs) $ printErrors src (errors vs)
              liftIO $ print (equivalent (modl s) t' u')
              modify (\s -> s{validationState = vs})
    
    handleNormalise src = do
      s <- get
      case runLexer parseType interactivePath src of
        Left es -> printErrors src es
        Right t -> case runValidation (validationState s) do
            scopeType (scopingCtx s) t >>= Kinding.synth (modl s) Map.empty
          of Left es -> do 
              printErrors src es
             Right (t'', vs) -> do
              unless (null $ errors vs) $ printErrors src (errors vs)
              liftIO $ putStrLn (unparse (normalise (modl s) t''))
              modify (\s -> s{validationState = vs})

    handleGrammar src = do
      s <- get 
      case runLexer parseTypes interactivePath src of 
        Left es -> printErrors src es
        Right ts -> case runValidation (validationState s) do
            mapM (scopeType (scopingCtx s) >=> Kinding.synth (modl s) Map.empty) ts
          of Left es -> do 
              printErrors src es
             Right (ts', vs) -> do
              unless (null $ errors vs) $ printErrors src (errors vs)
              liftIO $ putStrLn (showGrammar (fromTypes (modl s) ts'))
              modify (\s -> s{validationState = vs})

printErrors :: String -> [Error] -> Repl ()
printErrors src es = liftIO $ putStrLn $ showErrors (Map.singleton interactivePath (lines src)) es

ini :: Repl ()
ini = liftIO $ putStrLn "STEquiv | A tool for testing type equivalence | :? for help"


fin :: Repl ExitDecision
fin = liftIO $ putStrLn "Come again!" >> pure Exit

repl :: IO ()
repl = flip evalStateT (ReplState emptyValidationState emptyScopingCtx M.emptyModule) $ evalRepl
  (pure . (++ " ") . ("stequiv" ++) . \case SingleLine -> ">"; MultiLine -> "|")
  cmd
  opts
  (Just optPrefix)
  (Just "m")
  (Prefix (wordCompleter byWord) defaultMatcher)
  ini
  fin

main :: IO ()
main = repl