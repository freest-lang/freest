{- |
Module      :  Compiler.Pipeline
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Loading FreeST source files: parsing, scoping, kinding and typing,
with or without the implicit Prelude. On success returns the scoped
module; on failure prints the errors and returns 'Nothing'.
-}
module Compiler.Pipeline
  ( validateModule
  , loadPrelude
  , loadModule
  , loadPreludeAndModule
  , loadSilent
  , loadNoModule
  ) where

import Syntax.Module qualified as M
import Syntax.Declarations qualified as D
import Parser.Parser ( runParseModule )
import Parser.Scoping ( scopeModule', emptyScopingCtx, ScopingCtx )
import Validation.Base ( Validation, ValidationState, emptyValidationState, runValidation )
import Validation.HOTRecursion ( checkNoHOTRec )
import Validation.SessionPattern ( checkNoVarsInSessionPatterns )
import Validation.Kinding ( kindModule, KindCtx, emptyKindCtx )
import Validation.Typing ( typeModule, TypeCtx, emptyTypeCtx )
import UI.CLI ( preludePath, moduleLoaded, noModuleLoaded, preludeNotLoaded, failedToLoadModule, notASourceFile )
import UI.Error ( printErrors, Source )
import Paths_freest ( getDataFileName )

import Control.Exception ( IOException, try )
import Control.Monad.State ( get )
import Data.Map qualified as Map
import System.IO ( stderr, hPutStrLn )

-- | Scope a parsed module against an existing scoping context, then kind
-- and type it. The @prior@ kinded module supplies the data-level declarations
-- already in scope (from earlier REPL inputs or a loaded module), so a new
-- input may mention constructors, datatypes and type aliases declared earlier
-- — notably in constructor patterns, which 'typeModule' resolves against the
-- module's 'dataConsDecls'. Only the new module's own definitions are type-checked.
-- Returns the extended contexts and the new module's kinded form (its own
-- declarations with the inherited ones folded in).
validateModule :: ScopingCtx -> KindCtx -> TypeCtx
               -> D.KindedTypeDecls -> D.KindedDataDecls
               -> M.ParsedModule
               -> Validation (ScopingCtx, KindCtx, TypeCtx, M.KindedModule)
validateModule sctx kctx tctx tdecls ddecls modl = do
  (sctx', smodl) <- scopeModule' sctx modl
  (kctx', kmodl) <- kindModule kctx smodl
  checkNoHOTRec (M.typeDecls kmodl)
  (kmodl', kctx'', tctx') <- typeModule kctx' tctx (inheritDecls kmodl)
  checkNoVarsInSessionPatterns (M.definitions kmodl')
  pure (sctx', kctx'', tctx', kmodl')
  where
  inheritDecls m = m
    { M.typeDecls = M.typeDecls m `Map.union` tdecls
    , M.dataDecls = M.dataDecls m <>          ddecls
    }

-- | A snapshot of all state produced by a successful module load:
-- the source map (for error reporting), the running 'ValidationState',
-- the scoping, kinding and typing contexts, and the 'KindedModule'.
type LoadState = (Source, ValidationState, ScopingCtx, KindCtx, TypeCtx, M.KindedModule)

-- | Load just the Prelude.
loadPrelude :: IO (Maybe LoadState)
loadPrelude = do
  p <- getDataFileName preludePath
  loadM (putStrLn noModuleLoaded) [p]

-- | Load a program module on its own (no Prelude).
loadModule :: FilePath -> IO (Maybe LoadState)
loadModule programPath = do
  putStrLn preludeNotLoaded
  loadM (putStrLn moduleLoaded) [programPath]

-- | Load no module at all, just print a message to that effect,
-- thus centralising all module loading messages in this module.
loadNoModule :: IO ()
loadNoModule = putStrLn preludeNotLoaded >> putStrLn noModuleLoaded

-- | Load the Prelude joined with a program module: read both, merge their
-- parses into a single 'ParsedModule', then validate the whole.
loadPreludeAndModule :: FilePath -> IO (Maybe LoadState)
loadPreludeAndModule programPath = do
  preludeFile <- getDataFileName preludePath
  loadM (putStrLn moduleLoaded) [preludeFile, programPath]

-- | Load a program silently (no status banners), so a batch run's stdout
-- carries only the program's own output. @withPrelude@ selects whether the
-- implicit Prelude is loaded alongside the program.
loadSilent :: Bool -> FilePath -> IO (Maybe LoadState)
loadSilent withPrelude programPath = do
  files <- if withPrelude
             then (: [programPath]) <$> getDataFileName preludePath
             else pure [programPath]
  loadM (pure ()) files

-- | Read the given files, parse them, merge into a single 'ParsedModule',
-- then scope, kind and type-check it. The 'post' action runs on successful
-- load (pass 'pure ()' to remain silent). On failure (any unreadable file,
-- parse error, or validation error), prints errors against all sources and
-- returns 'Nothing'.
loadM :: IO () -> [FilePath] -> IO (Maybe LoadState)
loadM post paths =
  traverse tryRead paths >>= maybe (pure Nothing) (validate . zip paths) . sequence
  where
    validate inputs =
      let srcs = Map.fromList [(p, lines s) | (p, s) <- inputs] in
      case do modules <- mapM (uncurry runParseModule) inputs
              runValidation emptyValidationState do
                (sctx, kctx, tctx, kmodl) <- validateModule emptyScopingCtx emptyKindCtx emptyTypeCtx Map.empty D.emptyDataDecls (mconcat modules)
                vs                        <- get
                pure (srcs, vs, sctx, kctx, tctx, kmodl)
      of Left es -> do
          printErrors srcs es
          hPutStrLn stderr failedToLoadModule
          pure Nothing
         Right result -> do
          post
          pure (Just result)

-- | Try to read a file; on IO failure print 'notASourceFile' and return
-- 'Nothing', otherwise return the file contents wrapped in 'Just'.
tryRead :: FilePath -> IO (Maybe String)
tryRead path = do
  result <- try (readFile path) :: IO (Either IOException String)
  case result of
    Left _  -> Nothing <$ hPutStrLn stderr (notASourceFile path)
    Right s -> pure (Just s)
