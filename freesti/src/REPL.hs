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

import Syntax.Base ( getSpan, Variable )
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Syntax.Expression qualified as E
import Parser.Lexer ( layoutSC )
import Parser.LexerUtils ( runLexer, pushStartCode, Lexer )
import Parser.Parser ( parseType, parseExp, parseTwoTypes, parseTypes, parseDeclList, parseItDecl )
import Parser.Scoping qualified as Scoping
import Parser.Unparser ( unparse )
import Validation.Base ( Validation, ValidationState(..), emptyValidationState, runValidation )
import Validation.Normalisation ( normalise )
import Validation.TypeEquivalence ( equivalent, showGrammar, fromTypes )
import Validation.Kinding qualified as Kinding
import Validation.Typing qualified as Typing
import Load qualified
import UI.Error ( printErrors, Error )
import UI.CLI ( version, freeSTiPrompt, comeAgain, interactivePath, optPrefix )

import Data.List qualified as List
import Data.Map qualified as Map
import Control.Monad.State
    ( (>=>),
      modify,
      evalStateT,
      MonadIO(..),
      MonadState(get, put), gets,
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
import Control.Monad.Except (runExceptT)

-- The state of the REPL

data ReplState = ReplState
  { implicitPrelude :: Bool
  , filePath        :: Maybe FilePath
  , validationState :: ValidationState
  , scopingCtx      :: Scoping.ScopingCtx
  , kindCtx         :: Kinding.KindCtx
  , typeCtx         :: Typing.TypeCtx
  , modl            :: M.ScopedModule
  , valueCtx        :: ValueCtx
  }

emptyReplState :: ReplState
emptyReplState = ReplState
  { implicitPrelude = False
  , filePath        = Nothing
  , validationState = emptyValidationState
  , scopingCtx      = Scoping.emptyScopingCtx
  , kindCtx         = Kinding.emptyKindCtx
  , typeCtx         = Typing.emptyTypeCtx
  , modl            = M.emptyScopedModule
  , valueCtx        = Map.empty
  }

instance Show ReplState where
  show s = unlines
    [ "ReplState {"
    , "  implicitPrelude = " ++ show (implicitPrelude s)
    , "  filePath = " ++ show (filePath s)
    , "  validationState = { errors = " ++ show (length (errors (validationState s)))
                             ++ ", counter = " ++ show (counter (validationState s)) ++ " }"
    , "  scopingCtx = " ++ show (scopingCtx s)
    , "  kindCtx = " ++ show (kindCtx s)
    , "  typeCtx = " ++ show (typeCtx s)
    , "  modl = " ++ show (modl s)
    , "  valueCtx = " ++ show (valueCtx s)
    , "}"
    ]

-- The REPL itself

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
  where
    prefixedOpts :: [String]
    prefixedOpts = map ((optPrefix :) . fst) replOpts
    -- Prefix tab completeter
    defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
    defaultMatcher = map (, listCompleter []) prefixedOpts
    -- Default tab completer
    byWord :: Monad m => WordCompleter m
    byWord n = return $ filter (List.isPrefixOf n) prefixedOpts
    -- The various REPL commands, mapped to their handlers
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

-- The REPL commands

type Repl a = HaskelineT (StateT ReplState IO) a

ini :: Repl ()
ini = do
  liftIO $ putStrLn $ version ++ ", :h for help"
  s <- get
  case filePath s of
    Just path                   -> handleLoad path
    Nothing | implicitPrelude s -> runLoader Load.loadPrelude
            | otherwise         -> liftIO Load.loadNoModule

-- | Run a loader action and, on success, replace the validation/scoping/type
-- contexts and module in the REPL state with whatever the loader produced.
runLoader :: IO (Maybe (ValidationState, Scoping.ScopingCtx, Typing.TypeCtx, M.ScopedModule)) -> Repl ()
runLoader loader =
  liftIO loader >>= \case
    Nothing -> pure ()
    Just (vs, sctx, tctx, smodl) ->
      modify (\s -> s{validationState = vs, scopingCtx = sctx, typeCtx = tctx, modl = smodl})

fin :: Repl ExitDecision
fin = liftIO $ putStrLn comeAgain >> pure Exit

cmd :: String -> Repl ()
cmd src =
  -- First try a bare expression, bound to 'it'
  case runLexer parseItDecl interactivePath (src ++ "\n") of
    Right m1 -> handleModule m1 (liftIO $ putStrLn "Printing the value of variable 'it'")
    Left es1 ->
      -- Otherwise try a (possibly multi-line) block of let declarations
      case runLexer (pushStartCode layoutSC >> parseDeclList) interactivePath (src ++ "\n") of
        Right m2 -> handleModule m2 (pure ())
        Left es2 -> printREPLErrors src -- Lexer/parser errors
          (if getSpan (head es1) > getSpan (head es2) then es1 else es2)
  where
    -- | Validate parsed declarations. On success: update the remaining state
    -- fields, evaluate, run 'post'. On failure: report the errors.
    handleModule :: M.ParsedModule -> Repl () -> Repl ()
    handleModule m post =
      runValidate src validateModule m \(sctx, kctx, tctx, merged) -> do
        modify (\s -> s{scopingCtx = sctx, kindCtx = kctx, typeCtx = tctx, modl = merged})
        eval merged
        post

-- TODO: handle relative paths
handleLoad :: FilePath -> Repl () -- freesti> :l <file>
handleLoad path = do
  modify (\s -> s{filePath = Just path})
  ip <- gets implicitPrelude
  let loader = if ip then Load.loadPreludeAndModule else Load.loadModule
  runLoader (loader path)

handleReload :: FilePath -> Repl () -- freesti> :r
handleReload "" =
  gets filePath >>= maybe (liftIO Load.loadNoModule) handleLoad
handleReload _  =
  liftIO $ putStrLn "'reload' takes no arguments, just type ':r' to reload the current module"

-- | Parse the input and hand the parsed value to the validate/output half.
-- Parser errors are reported against the interactive source.
runPipeline :: String                           -- source code
           -> Lexer a                           -- parse
           -> (ReplState -> a -> Validation b)  -- validate
           -> (b -> Repl ())                    -- output
           -> Repl ()
runPipeline src parse validate output =
  case runLexer parse interactivePath src of
    Left es -> printREPLErrors src es -- Lexer/parser errors
    Right x -> runValidate src validate x output

-- | Run the validation, threading the validation state forward; on success
-- update 'validationState' and hand the result to 'output'; on failure print
-- the errors.
runValidate :: String                            -- source code (for error reporting)
            -> (ReplState -> a -> Validation b)  -- validate
            -> a                                 -- parsed input
            -> (b -> Repl ())                    -- output
            -> Repl ()
runValidate src validate x output = do
  s <- get
  case runState (runExceptT (validate s x)) (validationState s) of
    (Left e,  ValidationState{errors}) -> printREPLErrors src (e : errors)
    (Right y, vs@ValidationState{errors})
      | null errors -> modify (\s' -> s'{validationState = vs}) >> output y
      | otherwise   -> printREPLErrors src errors

handleKind :: String -> Repl () -- freesti> :k <type>
handleKind src = runPipeline src parseType
  validateType
  (\t' -> liftIO $ putStrLn (src ++ " : " ++ unparse (TK.kindOf t')))

handleEquivalent :: String -> Repl () -- freesti> :e <type1> <type2>
handleEquivalent src = runPipeline src parseTwoTypes
  (\s (t, u) -> validateTypes s [t, u])
  (\(kmodl, [t', u']) -> liftIO $ print (equivalent kmodl t' u'))

handleNormalise :: String -> Repl () -- freesti> :n <type>
handleNormalise src = runPipeline src parseType
  (\s t -> validateTypes s [t])
  (\(kmodl, [t']) -> liftIO $ putStrLn (unparse (normalise kmodl t')))

handleGrammar :: String -> Repl () -- freesti> :g <types>
handleGrammar src = runPipeline src parseTypes
  validateTypes
  (\(kmodl, ts') -> liftIO $ putStrLn (showGrammar (fromTypes kmodl ts')))

handleType :: String -> Repl () -- freesti> :t <exp>
handleType src = runPipeline src parseExp
  validateExp
  (\t -> liftIO $ putStrLn (src ++ " : " ++ unparse t))

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
handleState _ = get >>= liftIO . print

-- Validating syntax

-- | Scope and kind-synthesize a parsed type.
validateType :: ReplState -> TU.ParsedType -> Validation TK.KindedType
validateType s = Scoping.scopeType (scopingCtx s) >=> Kinding.synth (modl s) (kindCtx s)

-- | Kind the current module and scope/kind-synthesize a list of parsed types
-- against it. The result list has the same length and order as the input.
validateTypes :: ReplState -> [TU.ParsedType] -> Validation (M.KindedModule, [TK.KindedType])
validateTypes s ts = do
  kmodl <- Kinding.kindModule (modl s)
  ts'   <- mapM (validateType s) ts
  pure (kmodl, ts')

-- | Scope, kind and type-synthesize a parsed expression.
validateExp :: ReplState -> E.ParsedExp -> Validation TK.KindedType
validateExp s e = do
  kmodl  <- Kinding.kindModule (modl s)
  scoped <- Scoping.scopeExp (scopingCtx s) e
  kexp   <- Kinding.kindExp (modl s) kmodl (kindCtx s) scoped
  fst <$>   Typing.synth kmodl (kindCtx s) (typeCtx s) kexp

-- | Scope, kind and type-check a parsed module against the REPL's current
-- state, merging into the existing scoped module. 'kindCtx' is unchanged.
validateModule :: ReplState -> M.ParsedModule
                -> Validation (Scoping.ScopingCtx, Kinding.KindCtx, Typing.TypeCtx, M.ScopedModule)
validateModule s m = do
  (sctx, merged, tctx) <- Load.validateModule (scopingCtx s) (modl s) m
  pure (sctx, kindCtx s, tctx, merged)

-- | Print a list of errors against the interactive source line(s).
printREPLErrors :: FilePath -> [Error] -> Repl ()
printREPLErrors src es =
  liftIO $ printErrors (Map.singleton interactivePath (lines src)) es

-- Evaluation; interface with module Eval

type Value = ()
type ValueCtx = Map.Map Variable Value

eval :: M.ScopedModule -> Repl ()
eval m = do
  liftIO $ putStrLn "Evaluating..."
  s <- get
  vctx <- collectLetDecls (valueCtx s) m
  put s{valueCtx = vctx}

collectLetDecls :: ValueCtx -> M.ScopedModule -> Repl ValueCtx
collectLetDecls env _ = pure env