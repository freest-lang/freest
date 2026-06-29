{- |
Module      :  Compiler.REPL
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The interactive read-eval-print loop used by the FreeSTi interpreter.
-}
module Compiler.REPL
  ( ReplState(..)
  , emptyReplState
  , repl
  ) where

import Syntax.Base ( getSpan, Variable, external )
import Syntax.Module qualified as M
import Syntax.Declarations qualified as D
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Syntax.Expression qualified as E
import Parser.Lexer ( layoutSC )
import Parser.LexerUtils ( runLexer, pushStartCode, Lexer )
import Parser.Parser ( parseType, parseExp, parseTwoTypes, parseTypes, parseDeclList, parseItDecl, parseVariable, parseIdentifier )
import Parser.Scoping qualified as Scoping
import Parser.Unparser ( Unparse, unparse, unparseDataDef, unparseTypeDef )
import Validation.Base ( Validation, ValidationState(..), emptyValidationState, runValidation )
import Validation.Normalisation ( normalise )
import Validation.TypeEquivalence ( equivalent, showGrammar, fromTypes )
import Validation.Kinding qualified as Kinding
import Validation.Typing qualified as Typing
import Compiler.Pipeline qualified as Pipeline
import Interpreter.Value ( ValueCtx, emptyValueCtx )
import Interpreter.Eval ( evalModule )
import UI.Error ( printErrors, Error, Source )
import Interpreter.Exception ( printException )
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
import Control.Exception (try)

-- The state of the REPL

data ReplState = ReplState
  { implicitPrelude :: Bool
  , filePath        :: Maybe FilePath
  , source          :: Source
  , interactiveNo   :: Int
  , validationState :: ValidationState
  , scopingCtx      :: Scoping.ScopingCtx
  , kindCtx         :: Kinding.KindCtx
  , typeCtx         :: Typing.TypeCtx
  , tdecls          :: D.KindedTypeDecls
  , ddecls          :: D.KindedDataDecls
  , valueCtx        :: ValueCtx
  }

emptyReplState :: ReplState
emptyReplState = ReplState
  { implicitPrelude = False
  , filePath        = Nothing
  , source          = Map.empty
  , interactiveNo   = 0
  , validationState = emptyValidationState
  , scopingCtx      = Scoping.emptyScopingCtx
  , kindCtx         = Kinding.emptyKindCtx
  , typeCtx         = Typing.emptyTypeCtx
  , tdecls          = Map.empty
  , ddecls          = D.emptyDataDecls
  , valueCtx        = Map.empty
  }

instance Show ReplState where
  show s = unlines
    [ "ReplState {"
    , "  implicitPrelude = " ++ show (implicitPrelude s)
    , "  filePath = " ++ show (filePath s)
    , "  source = " ++ show (source s)
    , "  interactiveNo = " ++ show (interactiveNo s)
    , "  validationState = { errors = " ++ show (length (errors (validationState s)))
                             ++ ", counter = " ++ show (counter (validationState s)) ++ " }"
    , "  scopingCtx = " ++ show (scopingCtx s)
    , "  kindCtx = " ++ show (kindCtx s)
    , "  typeCtx = " ++ show (typeCtx s)
    , "  tdecls = " ++ show (Map.keys (tdecls s))
    , "  ddecls = " ++ show (Map.keys (D.ddTypes (ddecls s)))
    , "  valueCtx = " ++ show (Map.keys (valueCtx s))
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

type Repl a = HaskelineT (StateT ReplState IO) a

ini :: Repl ()
ini = do
  putLines [version ++ ", :h for help"]
  s <- get
  case filePath s of
    Just path                   -> handleLoad path
    Nothing | implicitPrelude s -> runLoader Pipeline.loadPrelude
            | otherwise         -> liftIO Pipeline.loadNoModule

-- | Run a loader action and, on success, replace the validation/scoping/type
-- contexts and module in the REPL state with whatever the loader produced, and
-- evaluate the loaded module into a fresh value environment.
runLoader :: IO (Maybe (Source, ValidationState, Scoping.ScopingCtx, Kinding.KindCtx, Typing.TypeCtx, M.KindedModule)) -> Repl ()
runLoader loader =
  liftIO loader >>= \case
    Nothing -> pure ()
    Just (src, vs, sctx, kctx, tctx, kmodl) -> do
      vctx <- liftIO (try (evalModule emptyValueCtx kmodl)) >>= \case
        Right v -> pure v
        Left e  -> liftIO (printException src e) >> pure emptyValueCtx   -- e.g. main failed at load
      modify (\s -> s{source = src, validationState = vs, scopingCtx = sctx, kindCtx = kctx, typeCtx = tctx, tdecls = M.typeDecls kmodl, ddecls = M.dataDecls kmodl, valueCtx = vctx})

fin :: Repl ExitDecision
fin = putLines [comeAgain] >> pure Exit

cmd :: String -> Repl ()
cmd src = do
  path <- nextInteractivePath
  modify (\s -> s{source = Map.insert path (lines src) (source s)})
  -- First try a bare expression, bound to 'it'
  case runLexer parseItDecl path (src ++ "\n") of
    Right m1 -> handleModule m1 printIt
    Left es1 ->
      -- Otherwise try a (possibly multi-line) block of let declarations
      case runLexer (pushStartCode layoutSC >> parseDeclList) path (src ++ "\n") of
        Right m2 -> handleModule m2 (const (pure ()))
        Left es2 -> printREPLErrors -- Lexer/parser errors
          (if getSpan (head es1) > getSpan (head es2) then es1 else es2)
  where
    -- | Validate parsed declarations. On success: update the remaining state
    -- fields, evaluate, run 'post' on the typed module. On failure: report the
    -- errors.
    handleModule :: M.ParsedModule -> (M.KindedModule -> Repl ()) -> Repl ()
    handleModule m post =
      runValidate src validateModule m printREPLErrors \(sctx, kctx, tctx, kmodl) -> do
        modify (\s -> s
          { scopingCtx = sctx
          , kindCtx = kctx
          , typeCtx = tctx
          , tdecls = M.typeDecls kmodl
          , ddecls = M.dataDecls kmodl })
        eval kmodl
        post kmodl

-- Handling the various options

-- TODO: handle relative paths
handleLoad :: FilePath -> Repl () -- freesti> :l <path>
handleLoad path = do
  modify (\s -> s{filePath = Just path})
  ip <- gets implicitPrelude
  let loader = if ip then Pipeline.loadPreludeAndModule else Pipeline.loadModule
  runLoader (loader path)

handleReload :: String -> Repl () -- freesti> :r
handleReload "" =
  gets filePath >>= maybe (liftIO Pipeline.loadNoModule) handleLoad
handleReload _  =
  putLines ["'reload' takes no arguments, just type ':r' to reload the current module"]

handleKind :: String -> Repl () -- freesti> :k <type>
handleKind src = runPipeline src parseType validateType (printAs src . TK.kindOf)

handleType :: String -> Repl () -- freesti> :t <exp>
handleType src = runPipeline src parseExp validateExp (printAs src)

handleEquivalent :: String -> Repl () -- freesti> :e <type1> <type2>
handleEquivalent src = runPipeline src parseTwoTypes
    (\s (t, u) -> validateTypes s [t, u])
    (\[t', u'] -> get >>= \s -> putLines [show (equivalent (tdecls s) t' u')])

handleNormalise :: String -> Repl () -- freesti> :n <type>
handleNormalise src = runPipeline src parseType
  (\s t -> validateTypes s [t])
  (\[t'] -> get >>= \s -> putLines [unparse (normalise (tdecls s) t')])

handleGrammar :: String -> Repl () -- freesti> :g <type1> .., <typen>
handleGrammar src = runPipeline src parseTypes
  validateTypes
  (\ts' -> get >>= \s -> putLines [showGrammar (fromTypes (tdecls s) ts')])

handleInfo :: String -> Repl () -- freesti> :i <id>
handleInfo src = do
  path <- currentInteractivePath
  s <- get
  case runLexer parseVariable path src of
    Right v -> -- input is a lowercase name; try as an expression, then as a type
      let sp = getSpan v in
      case runValidation (validationState s) (validateExp s (E.Var sp v)) of
        Right t -> do -- bound at the expression level: print its type
          putLines [src ++ " is an expression variable"]
          printAs src t
        Left _  -> case runValidation (validationState s) (validateType s (TU.Var sp v)) of
          Right t -> do -- bound at the type level: print its kind
            putLines [src ++ " is a type variable"]
            printAs src (TK.kindOf t)
          Left _ -> notInScope -- neither expression nor type variable
    Left _ -> case runLexer parseIdentifier path src of
      Right i -> -- input is an uppercase name; look it up in the declarations
        case Map.lookup i (D.ddCons (ddecls s)) of
          Just (parent, _) -> do -- it's a data constructor: print its parent and its type
            putLines [src ++ " is a constructor of datatype " ++ show parent]
            case Map.lookup (Right i) (typeCtx s) of
              Just t  -> printAs src t -- type known: print it
              Nothing -> pure ()       -- type absent from the context: skip
          Nothing
            | Map.member i (D.ddTypes (ddecls s)) -> putLines -- it's a datatype: print kind sig and definition
                [ src ++ " is a datatype"
                , maybe "" (\k -> "type " ++ show i ++ " : " ++ unparse k)
                           (Map.lookup (Right i) (kindCtx s))
                , unparseDataDef (ddecls s) i
                ]
            | otherwise -> case Map.lookup i (tdecls s) of
              Just (hasParams, t) -> putLines -- it's a type name: print kind sig and definition
                [ src ++ " is a type"
                , maybe "" (\k -> "type " ++ show i ++ " : " ++ unparse k)
                           (Map.lookup (Right i) (kindCtx s))
                , unparseTypeDef i hasParams t
                ]
              Nothing -> notInScope -- not a constructor, datatype, or type name
      Left _ -> putLines [":i takes a single identifier"] -- input is neither a variable nor an identifier
  where
    notInScope :: Repl ()
    notInScope = putLines [src ++ " is not in scope"]

handleHelp :: String -> Repl () -- freesti> :h
handleHelp args = putLines
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

handleState :: String -> Repl () -- freesti> :s
handleState _ = get >>= liftIO . print

-- Running pipelines

-- | Parse the input and hand the parsed value to the validate/output half.
-- Parser errors are reported against the interactive source.
runPipeline :: String                           -- source code
           -> Lexer a                           -- parse
           -> (ReplState -> a -> Validation b)  -- validate
           -> (b -> Repl ())                    -- continuation
           -> Repl ()
runPipeline src parse validate continuation = do
  n <- gets interactiveNo
  modify (\s -> s{source = Map.insert (interactivePath n) (lines src) (source s), interactiveNo = n + 1})
  case runLexer parse (interactivePath n) src of
    Left es -> printREPLErrors es -- Lexer/parser errors
    Right x -> runValidate src validate x printREPLErrors continuation

-- | Run the validation, threading the validation state forward; on success
-- update 'validationState' and hand the result to 'output'; on failure print
-- the errors.
runValidate :: String                            -- source code (for error reporting)
            -> (ReplState -> a -> Validation b)  -- validate
            -> a                                 -- parsed input
            -> ([Error] -> Repl ())              -- error action (for accumulated errors)
            -> (b -> Repl ())                    -- continuation
            -> Repl ()
runValidate src validate x errAction continuation = do
  s <- get
  case runState (runExceptT (validate s x)) (validationState s) of
    (Left e,  ValidationState{errors}) -> printREPLErrors (e : errors)
    (Right y, vs@ValidationState{errors})
      | null errors -> modify (\s' -> s'{validationState = vs}) >> continuation y
      | otherwise   -> errAction errors

-- Printing results
-- | Print a list of errors against the interactive source line(s).
printREPLErrors :: [Error] -> Repl ()
printREPLErrors es = do
  source <- gets source
  liftIO $ printErrors source es

-- | @printAs src x@ prints @src ++ " : " ++ unparse x@ to stdout.
printAs :: Unparse a => String -> a -> Repl ()
printAs src x = putLines [src ++ " : " ++ unparse x]

-- | Print the given lines, skipping empty ones.
putLines :: [String] -> Repl ()
putLines = liftIO . putStr . unlines . filter (not . null)

-- Interactive path

nextInteractivePath :: Repl FilePath
nextInteractivePath = do
  n <- gets interactiveNo
  modify (\s -> s{interactiveNo = n + 1})
  pure (interactivePath n)

currentInteractivePath :: Repl FilePath
currentInteractivePath = do
  n <- gets interactiveNo
  pure (interactivePath n)

-- Validating syntax

-- | Scope and kind-synthesize a parsed type.
validateType :: ReplState -> TU.ParsedType -> Validation TK.KindedType
validateType s =
  Scoping.scopeType (scopingCtx s) >=>
  Kinding.kindType (kindCtx s)

-- | Kind the current module and scope/kind-synthesize a list of parsed types
-- against it. The result list has the same length and order as the input.
validateTypes :: ReplState -> [TU.ParsedType] -> Validation [TK.KindedType]
validateTypes = mapM . validateType

-- | Scope, kind and type-synthesize a parsed expression.
validateExp :: ReplState -> E.ParsedExp -> Validation TK.KindedType
validateExp s =
  Scoping.scopeExp (scopingCtx s)
  >=> Kinding.kindExp (tdecls s) (ddecls s) (kindCtx s)
  >=> Typing.synth (tdecls s) (ddecls s) (kindCtx s) (typeCtx s)
  >=> pure . \(_, t, _) -> t

-- | Scope, kind and type-check a parsed module against the REPL's current
-- state, merging into the existing scoped module.
validateModule :: ReplState -> M.ParsedModule
                -> Validation (Scoping.ScopingCtx, Kinding.KindCtx, Typing.TypeCtx, M.KindedModule)
validateModule s =
  Pipeline.validateModule (scopingCtx s) (kindCtx s) (typeCtx s) (tdecls s) (ddecls s)

-- Evaluation; interface with module Interpreter.Eval

-- | Evaluate a parsed-and-typed module: extend the value environment with its
-- definitions (running their side effects), threading it through the state.
eval :: M.KindedModule -> Repl ()
eval m = do
  s <- get
  liftIO (try (evalModule (valueCtx s) m)) >>= \case
    Right vctx -> put s{valueCtx = vctx}
    Left e     -> liftIO (printException (source s) e)   -- TODO: keep the old ctx, or not?

-- | Print the value bound to @it@ (an expression entered at the prompt
-- becomes the binding @it = …@).
printIt :: M.KindedModule -> Repl ()
printIt kmodl = do
  vctx <- gets valueCtx
  case [ var | E.ValDef (E.VarPat _ var) _ <- M.definitions kmodl, external var == "it" ] of
    itVar : _ -> mapM_ (\v -> putLines [unparse v]) (Map.lookup itVar vctx)
    []        -> pure ()