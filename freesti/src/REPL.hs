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

import Syntax.Base ( Located(spanFromTo), Span(..) )
import Syntax.Command ( Command(..) )
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Syntax.Expression qualified as E
import Parser.Lexer ( layoutSC )
import Parser.LexerUtils ( runLexer, pushStartCode )
import Parser.Parser ( parseType, parseExp, parseTwoTypes, parseTypes, parseCommand, runParseModule )
import Parser.Scoping
  ( ScopingCtx, scopeModule, emptyScopingCtx, scopeType, scopeExp, freshInternal, insertTId, insertDId )
import Parser.Unparser ( unparse )
import Validation.Base ( Validation, ValidationState (..), emptyValidationState, runValidation )
import Validation.Normalisation ( normalise )
import Validation.TypeEquivalence ( equivalent, showGrammar, fromTypes )
import Validation.Kinding qualified as Kinding
import Validation.Typing qualified as Typing
import Load qualified
import UI.Error ( printErrors, Error(..), Source )
import UI.CLI ( version, preludePath, freeSTiPrompt, moduleLoaded, noModuleLoaded, comeAgain, interactivePath, optPrefix )
import Utils (internalError)
import Paths_freest ( getDataFileName )

import Control.Monad.State
    ( (>=>),
      foldM,
      unless,
      when,
      modify,
      evalStateT,
      MonadIO(..),
      MonadState(get),
      StateT )
import Data.Bitraversable (bimapM)
import Data.List qualified as List
import Data.Map qualified as Map
import System.Console.Repline
    ( CompletionFunc,
      evalRepl,
      listCompleter,
      wordCompleter,
      CompleterStyle(Prefix),
      ExitDecision(Exit),
      HaskelineT,
      MultiLine(MultiLine, SingleLine),
      WordCompleter )
import Data.Maybe (isJust)
import System.Exit ( exitSuccess )
import Debug.Trace (traceM, trace)

{- Text produced by my good friend Claude
Longer-term alternative (worth considering)
Since the REPL re-kinds the whole module on every type query, you'll eventually want to cache it. The natural shape is to extend ReplState with a derived kindedModl :: M.KindedModule field that's refreshed whenever the Decls branch (currently stubbed at line 100) inserts new declarations. Then Kinding.synth keeps using the ScopedModule, while equivalent / normalise / fromTypes consume the cached KindedModule directly. While the Decls branch is still internalError, the modules are always empty, so the per-call conversion suggested above is essentially free — but it's worth wiring up the cache at the same time you implement Decls}
-}
data ReplState = ReplState
  { validationState :: ValidationState
  , scopingCtx :: ScopingCtx
  , typeCtx :: Typing.TypeCtx
  , modl :: M.ScopedModule
  , implicitPrelude :: Bool
  , filePath :: Maybe FilePath
  }

emptyReplState :: ReplState
emptyReplState = ReplState
  { validationState = emptyValidationState
  , scopingCtx = emptyScopingCtx
  , typeCtx = Typing.emptyTypeCtx
  , modl = M.emptyScopedModule
  , implicitPrelude = False
  , filePath = Nothing
  }

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
      | otherwise -> liftIO $ putStrLn noModuleLoaded

fin :: Repl ExitDecision
fin = liftIO $ putStrLn comeAgain >> pure Exit

cmd :: String -> Repl ()
cmd src = do
  s <- get
  case runLexer (pushStartCode layoutSC >> parseCommand) interactivePath (src ++ "\n") of
    Left es -> printREPLErrors src es -- Lexer/parser errors
    Right (Type t) ->
      case runValidation (validationState s) $
        scopeType (scopingCtx s) t >>= Kinding.synth (modl s) Map.empty
      of Left es -> printREPLErrors src es -- Validation errors
         Right t' -> do
          let vs = validationState s
          unless (null $ errors vs) $ printREPLErrors src (errors vs) -- TODO: needed?
          liftIO $ putStrLn (unparse t' ++ " : " ++ unparse (TK.kindOf t'))
          modify (\s -> s{validationState = vs}) -- TODO: needed?
    Right (Decls ds) -> do
        printREPLErrors src [UnsupportedError (Span interactivePath (1, 1) (1, length src + 1)) "Type declarations not yet implemented in the REPL" ""]
        -- let modl' = foldr insertKindSig (modl s) ds
        --     ctx' = foldr scopeEquation (scopingCtx s) ds
        -- case runValidation (validationState s) (foldM (insertEquation ctx') modl' ds) of
        --   Left es -> printREPLErrors src es
        --   Right (modl'', vs) -> do
        --     unless (null $ errors vs) $ printREPLErrors src (errors vs)
        --     modify \s -> s{scopingCtx = ctx', modl = modl''}

-- insertKindSig :: Equation -> M.ScopedModule -> M.ScopedModule
-- insertKindSig (i, map snd -> ks, t, k) m =
--   m{M.kindSigs = Map.insert i (buildArrow ks k) (M.kindSigs m)}
--   where buildArrow ks k = foldr (\k k' -> K.Arrow (spanFromTo k k') k k') k ks

-- scopeEquation :: Equation -> ScopingCtx -> ScopingCtx
-- scopeEquation (i, _, _, _) = insertTId i

-- insertEquation :: ScopingCtx -> M.KindedModule -> M.KindedModule -> Validation M.KindedModule
-- insertEquation ctx modl (i, aks, t, k) = do
--   t' <- scopeType ctx (if null aks then t else TU.Abs (spanFromTo i t) aks t)
--   t'' <- Kinding.check modl Map.empty t' (M.kindSigs modl Map.! i)
--   return modl{M.typeDecls = Map.insert i t'' (M.typeDecls modl)}

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
  , "For commands :equivalent and :grammar, which take multiple arguments, you may need"
  , "to use parenthesis to prevent type-level applications from being parsed as different"
  , "arguments. E.g., :g T U shows the grammar for types T and U while :g (T U) shows the"
  , "grammar for type T applied to U"
  ]
  where ind = ("  " ++)

handleInfo :: String -> Repl () -- freesti> :i <text>
handleInfo text = liftIO $ putStrLn "TODO: What do we want here?"

-- TODO: handle relative paths
handleLoad :: FilePath -> Repl () -- freesti> :l <file>
handleLoad path = do
  modify (\s -> s{filePath = Just path})
  s <- get
  let loader = if implicitPrelude s then Load.loadPreludeAndModule else Load.loadModule
  liftIO (loader path) >>= \case
    Nothing -> pure ()
    Just (sc, tc, sm) ->
      modify (\s' -> s'{typeCtx = tc, scopingCtx = sc, modl = sm})

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
        ts' <- mapM (kindAType s) ts
        pure (kmodl, ts')
      of Left es -> printREPLErrors src es
         Right (kmodl, ts') -> do
          liftIO $ putStrLn (showGrammar (fromTypes kmodl ts'))

-- | Scope and kind-synthesize a parsed type.
kindAType :: ReplState -> TU.ParsedType -> Validation TK.KindedType
kindAType s = scopeType (scopingCtx s) >=> Kinding.synth (modl s) Map.empty

-- | Scope, kind and type-synthesize a parsed expression.
typeAnExp :: ReplState -> E.ParsedExp -> Validation TK.KindedType
typeAnExp s e = do
  scoped <- scopeExp (scopingCtx s) e
  kmodl  <- Kinding.kindModule (modl s)
  kexp <- Kinding.kindExp (modl s) kmodl Map.empty scoped
  -- traceM (show scoped)
  -- traceM (show (typeCtx s))
  fst <$> Typing.synth kmodl Map.empty (typeCtx s) kexp

-- | Print a list of errors against the interactive source line(s).
printREPLErrors :: FilePath -> [Error] -> Repl ()
printREPLErrors src es =
  liftIO $ printErrors (Map.singleton interactivePath (lines src)) es
