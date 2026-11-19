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
  , loadPreludeAndModuleWithErrors
  , loadSilent
  , loadNoModule
  , LoadState
  ) where

import Syntax.Module qualified as M
import Syntax.Declarations qualified as D
import Parser.Parser ( runParseModule )
import Compiler.Include ( resolveIncludes, IncludeError(..) )
import Parser.Scoping ( scopeModule', emptyScopingCtx, ScopingCtx )
import Validation.Base ( Validation, ValidationState, emptyValidationState, runValidation )
import Validation.HOTRecursion ( checkNoHOTRec )
import Validation.SessionPattern ( checkNoVarsInSessionPatterns )
import Validation.Kinding ( kindModule, KindCtx, emptyKindCtx )
import Validation.Typing ( typeModule, TypeCtx, emptyTypeCtx )
import UI.CLI ( preludePath, moduleLoaded, noModuleLoaded, preludeNotLoaded, failedToLoadModule, notASourceFile )
import UI.Error ( printErrors, Source )
import Paths_freest ( getDataFileName )

import Control.Monad.State ( get )
import Data.Map qualified as Map
import Data.Functor ( ($>) )
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

-- | Load the Prelude joined with a program module without printing anything,
-- returning the failure for the caller to render (used by the language server).
-- Files in @virtualFiles@ are read from there, as in 'resolveIncludes'.
loadPreludeAndModuleWithErrors :: Source -> FilePath -> IO (Either IncludeError LoadState)
loadPreludeAndModuleWithErrors virtualFiles programPath = do
  preludeFile <- getDataFileName preludePath
  loadME virtualFiles [preludeFile, programPath]

-- | Expand the given roots along their 'INCLUDE' pragmas, parse each resulting
-- file, merge into a single 'ParsedModule', then scope, kind and type-check it.
loadME :: Source -> [FilePath] -> IO (Either IncludeError LoadState)
loadME virtualFiles roots = (>>= validate) <$> resolveIncludes virtualFiles roots
  where
    validate inputs =
      let srcs = Map.fromList inputs in
      either (Left . GraphErrors srcs) Right do
        modules <- mapM (uncurry runParseModule) inputs
        runValidation emptyValidationState do
          (sctx, kctx, tctx, kmodl) <- validateModule emptyScopingCtx emptyKindCtx emptyTypeCtx Map.empty D.emptyDataDecls (M.insertBuiltinLists (mconcat modules))
          vs                        <- get
          pure (srcs, vs, sctx, kctx, tctx, kmodl)

-- | 'loadME', printing errors against all sources on failure. The 'post'
-- action runs on successful load (pass 'pure ()' to remain silent).
loadM :: IO () -> [FilePath] -> IO (Maybe LoadState)
loadM post roots =
  loadME Map.empty roots >>= \case
    Left (InvalidRoot p)      -> abort (hPutStrLn stderr (notASourceFile p))
    Left (GraphErrors src es) -> abort (printErrors src es)
    Right result              -> post $> Just result
  where
    abort report = (report *> hPutStrLn stderr failedToLoadModule) $> Nothing
