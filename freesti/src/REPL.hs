{- |
Module      :  REPL
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The interactive read-eval-print loop used by the FreeSTi interpreter.
-}
module REPL
  ( ReplState(..)
  , emptyReplState
  , repl
  ) where

import Syntax.Base ( getSpan )
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Syntax.Expression qualified as E
import Parser.LexerUtils ( runLexer )
import Parser.Parser ( parseType, parseExp, parseTwoTypes, parseTypes, parsePatDecl, parseItPatDecl )
import Parser.Unparser ( unparse )
import Validation.Base ( Validation, ValidationState(..), emptyValidationState, runValidation )
import Validation.Normalisation ( normalise )
import Validation.TypeEquivalence ( equivalent, showGrammar, fromTypes )
import Parser.Scoping     qualified as Scoping
import Validation.Kinding qualified as Kinding
import Validation.Typing  qualified as Typing
import Load qualified
import UI.Error ( printErrors, Error )
import UI.CLI ( version, freeSTiPrompt, noModuleLoaded, comeAgain, interactivePath, optPrefix )

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Bitraversable (bimapM)
import Control.Monad.State
    ( (>=>),
      modify,
      evalStateT,
      MonadIO(..),
      MonadState(get),
      StateT, runState )
import System.Console.Repline
  ( CompletionFunc,
    evalRepl,
    listCompleter,
    wordCompleter,
    CompleterStyle(Prefix),
    ExitDecision(Exit),
    HaskelineT,
    MultiLine(MultiLine, SingleLine),
    WordCompleter
  )
import System.Exit ( exitSuccess )
import Debug.Trace (traceM)
import qualified Syntax.Module as Load
import Control.Monad.Except (runExceptT)

data ReplState = ReplState
  { validationState :: ValidationState
  , scopingCtx :: Scoping.ScopingCtx
  , kindCtx :: Kinding.KindCtx
  , typeCtx :: Typing.TypeCtx
  , modl :: M.ScopedModule
  , implicitPrelude :: Bool
  , filePath :: Maybe FilePath
  }

emptyReplState :: ReplState
emptyReplState = ReplState
  { validationState = emptyValidationState
  , scopingCtx = Scoping.emptyScopingCtx
  , kindCtx = Kinding.emptyKindCtx
  , typeCtx = Typing.emptyTypeCtx
  , modl = M.emptyScopedModule
  , implicitPrelude = False
  , filePath = Nothing
  }

instance Show ReplState where
  show s = unlines
    [ "ReplState {"
    , "  validationState = { errors = " ++ show (length (errors (validationState s)))
                                ++ ", counter = " ++ show (counter (validationState s)) ++ " }"
    , "  scopingCtx = " ++ show (scopingCtx s)
    , "  kindCtx = " ++ show (kindCtx s)
    , "  typeCtx = " ++ show (typeCtx s)
    , "  modl = " ++ show (modl s)
    , "  implicitPrelude = " ++ show (implicitPrelude s)
    , "  filePath = " ++ show (filePath s)
    , "}"
    ]

repl :: ReplState -> IO ()
repl =
  evalStateT
    (evalRepl
      (pure . (++ " ") . (freeSTiPrompt ++) . \case SingleLine -> ">"; MultiLine -> "|")
      cmd
      replOpts
      (Just optPrefix)
      (Just "m")
      (Prefix (wordCompleter byWord) defaultMatcher)
      ini
      fin
    )

type Repl a = HaskelineT (StateT ReplState IO) a

ini :: Repl ()
ini = do
  liftIO $ putStrLn $ version ++ ", :h for help"
  s <- get
  case filePath s of
    Just path -> handleLoad path
    Nothing
      | implicitPrelude s -> do
          liftIO Load.loadPrelude >>= \case
            Just (scopeCtx, typeCtx, scopedModule) ->
              modify (\s' -> s'{modl = scopedModule, typeCtx = typeCtx, scopingCtx = scopeCtx})
            Nothing     -> pure ()
      | otherwise -> liftIO Load.loadNoModule

fin :: Repl ExitDecision
fin = liftIO $ putStrLn comeAgain >> pure Exit

cmd :: String -> Repl ()
cmd src = do
  s <- get
  -- First try an expression
  case runLexer parsePatDecl interactivePath (src ++ "\n") of
    Left es1 ->
      -- If that fails, try a pattern
      case runLexer parseItPatDecl interactivePath (src ++ "\n") of
        Left es2 -> printREPLErrors src -- Lexer/parser errors
          (if getSpan (head es1) > getSpan (head es2) then es1 else es2)
        Right p2 -> do
          validateLetDecl s src p2
          eval p2
          liftIO $ putStrLn "Printing the value of variable 'it'"
    Right p1 -> do
      validateLetDecl s src p1
      eval p1
      -- print nothing

validateLetDecl :: ReplState -> String -> E.ParsedLetDecl -> Repl ()
validateLetDecl s src p = case runState (runExceptT (typeALetDecl s p)) (validationState s) of --  TODO: refactor runValidation?
  (Left e, ValidationState{errors}) -> printREPLErrors src (e : errors) -- Scoping/kinding/typing errors
  (Right (sctx, kctx, tctx), vs@ValidationState{errors})
    | null errors -> modify (\s -> s{validationState = vs, scopingCtx = sctx, kindCtx = kctx, typeCtx = tctx})
    | otherwise -> printREPLErrors src errors

eval :: E.ParsedLetDecl -> Repl ()
eval _ = liftIO $ putStrLn "Evaluating..."

prefixedOpts :: [String]
prefixedOpts = map ((optPrefix :) . fst) replOpts

-- Prefix tab completeter
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = map (, listCompleter []) prefixedOpts

-- Default tab completer
byWord :: Monad m => WordCompleter m
byWord n = return $ filter (List.isPrefixOf n) prefixedOpts

replOpts :: [(String, String -> Repl ())]
replOpts =
  [ ("?"         , handleHelp)
  , ("help"      , handleHelp)
  , ("state"     , handleState) -- remove when in production
  , ("info"      , handleInfo)
  , ("load"      , handleLoad)
  , ("reload"    , handleReload)
  , ("kind"      , handleKind)
  , ("type"      , handleType)
  , ("equivalent", handleEquivalent)
  , ("normalise" , handleNormalise)
  , ("grammar"   , handleGrammar)
  , ("quit"      , const $ liftIO exitSuccess)
  ]

handleHelp :: String -> Repl ()
handleHelp args = liftIO $ putStrLn $ unlines
  [ "Commands available from the prompt:"
  , ind "<type>                        show the normal form and kind of <type>"
  , ind "<typedecl>                    define a type (use :m for mutual recursion)"
  , ind ":load <file>                  load a module from a file"
  , ind ":reload                       reload the current module"
  , ind ":kind <type>                  show the kind of <type>"
  , ind ":info                         display not sure what"
  , ind ":normalise <type>             show the normal form of <type>"
  , ind ":equivalent <type1> <type2>   check if <type1> is equivalent to <type2>"
  , ind ":grammar <type1> ... <typen>  show the grammar for types <type1> through <typen>"
  , ind ":m                            enter multi-line mode"
  , ind ":?, :help                     display this list of commands"
  , ind ":state                        display the current state of the interpreter"
  , "(for : commands, writing a prefix is enough, e.g., :k <type>)"
  , ""
  , "Type equations need kind information for each parameter and for the right-hand side."
  , "If omitted, kinds default to *T. The syntax is as follows:"
  , ind "<equation> ::= type <upperId> (<lowerId> : <kind>) ... = <type> : <kind>"
  , ""
  , "For commands :equivalent and :grammar, which take multiple arguments, you may need"
  , "to use parenthesis to prevent type-level applications from being parsed as different"
  , "arguments. E.g., :g T U shows the grammar for types T and U while :g (T U) shows the"
  , "grammar for type T applied to U"
  ]
  where ind = ("  " ++)

handleInfo :: String -> Repl () -- freesti> :i <text>
handleInfo text = liftIO $ putStrLn "TODO: What do we want here?"

handleState :: String -> Repl () -- freesti> :s
handleState _ = get >>= liftIO . putStrLn . show

-- TODO: handle relative paths
handleLoad :: FilePath -> Repl () -- freesti> :l <file>
handleLoad path = do
  modify (\s -> s{filePath = Just path})
  s <- get
  let loader = if implicitPrelude s then Load.loadPreludeAndModule else Load.loadModule
  liftIO (loader path) >>= \case
    Nothing -> pure ()
    Just (sc, tc, sm) -> do
      modify (\s -> s{modl = sm, scopingCtx = sc, typeCtx = tc})

handleReload :: FilePath -> Repl () -- freesti> :r
handleReload "" = do
  s <- get
  case filePath s of
    Nothing   -> liftIO $ putStrLn noModuleLoaded
    Just path -> handleLoad path
handleReload _ =
  liftIO $ putStrLn "':reload' takes no arguments, just type ':reload' to reload the current module"

handleKind :: String -> Repl () -- freesti> :k <type>
handleKind src = do
  s <- get
  case runLexer parseType interactivePath src of
    Left es -> do
      printREPLErrors src es -- Lexer/parser errors
    Right t ->
      case runValidation (validationState s) (kindAType s t) of
        Left es -> printREPLErrors src es -- Scopping/kinding errors
        Right t' -> do
          liftIO $ putStrLn (src ++ " : " ++ unparse (TK.kindOf t'))

handleType :: String -> Repl () -- freesti> :t <exp>
handleType src = do
  s <- get
  case runLexer parseExp interactivePath src of
    Left es -> printREPLErrors src es -- Lexer/parser errors
    Right e ->
      case runValidation (validationState s) (typeAnExp s e) of
        Left es -> printREPLErrors src es -- Scopping/kinding/typing errors
        Right t -> do
          liftIO $ putStrLn (src ++ " : " ++ unparse t)

handleEquivalent :: String -> Repl () -- freesti> :e <type1> <type2>
handleEquivalent src = do
  s <- get
  case runLexer parseTwoTypes interactivePath src of
    Left es -> printREPLErrors src es -- Lexer/parser errors
    Right (t, u) ->
      case runValidation (validationState s) do
        kmodl <- Kinding.kindModule (modl s) -- TODO: cache in ReplState?
        tu' <- bimapM (kindAType s) (kindAType s) (t, u)
        pure (kmodl, tu')
      of Left es -> printREPLErrors src es -- Scopping/kinding errors
         Right (kmodl, (t', u')) -> do
          liftIO $ print (equivalent kmodl t' u')

handleNormalise :: String -> Repl () -- freesti> :n <type>
handleNormalise src = do
  s <- get
  case runLexer parseType interactivePath src of
    Left es -> printREPLErrors src es
    Right t ->
      case runValidation (validationState s) do
        kmodl <- Kinding.kindModule (modl s) -- TODO: cache in ReplState?
        t'    <- kindAType s t
        pure (kmodl, t')
      of Left es -> printREPLErrors src es
         Right (kmodl, t') -> do
          liftIO $ putStrLn (unparse (normalise kmodl t'))

handleGrammar :: String -> Repl () -- freesti> :g <types>
handleGrammar src = do
  s <- get
  case runLexer parseTypes interactivePath src of
    Left es -> printREPLErrors src es
    Right ts -> case runValidation (validationState s) do
        kmodl <- Kinding.kindModule (modl s) -- TODO: cache in ReplState?
        ts'   <- mapM (kindAType s) ts
        pure (kmodl, ts')
      of Left es -> printREPLErrors src es
         Right (kmodl, ts') -> do
          liftIO $ putStrLn (showGrammar (fromTypes kmodl ts'))

-- | Scope and kind-synthesize a parsed type.
kindAType :: ReplState -> TU.ParsedType -> Validation TK.KindedType
kindAType s = Scoping.scopeType (scopingCtx s) >=> Kinding.synth (modl s) (kindCtx s)

-- | Scope, kind and type-synthesize a parsed expression.
typeAnExp :: ReplState -> E.ParsedExp -> Validation TK.KindedType
typeAnExp s e = do
  scoped <- Scoping.scopeExp (scopingCtx s) e
  kmodl  <- Kinding.kindModule (modl s)
  kexp   <- Kinding.kindExp (modl s) kmodl (kindCtx s) scoped
  fst <$> Typing.synth kmodl (kindCtx s) (typeCtx s) kexp

-- | Scope, kind and type-check a parsed let declaration.
typeALetDecl :: ReplState -> E.ParsedLetDecl
             -> Validation (Scoping.ScopingCtx, Kinding.KindCtx, Typing.TypeCtx)
typeALetDecl s p = do
  kmodl <- Kinding.kindModule (modl s)
  (sctx, scoped) <- Scoping.scopeDefs (scopingCtx s) [p]
  (kctx, klds) <- Kinding.kindLetDecls (modl s) kmodl (kindCtx s) scoped
  (_, kctx, tctx) <- Typing.checkDecls kmodl kctx (typeCtx s) klds
  return (sctx, kctx, tctx)

-- | Print a list of errors against the interactive source line(s).
printREPLErrors :: FilePath -> [Error] -> Repl ()
printREPLErrors src es =
  liftIO $ printErrors (Map.singleton interactivePath (lines src)) es
