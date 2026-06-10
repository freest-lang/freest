{- |
Module      :  Pipeline
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Loading FreeST source files: parsing, scoping, kinding and typing,
with or without the implicit Prelude. On success returns the scoped
module; on failure prints the errors and returns 'Nothing'.
-}
module Pipeline
  ( validateModule
  , loadPrelude
  , loadModule
  , loadPreludeAndModule
  , loadNoModule
  ) where

import Syntax.Module qualified as M
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

-- | Scope a parsed module against an existing scoping context, then kind
-- and type it. Returns the extended contexts and the new module's kinded
-- form (not merged with any prior module — composition into a running
-- 'KindedModule' is the caller's responsibility).
validateModule :: ScopingCtx -> KindCtx -> TypeCtx -> M.ParsedModule
               -> Validation (ScopingCtx, KindCtx, TypeCtx, M.KindedModule)
validateModule sctx kctx tctx modl = do
  (sctx', smodl) <- scopeModule' sctx modl
  (kctx', kmodl) <- kindModule kctx smodl
  checkNoHOTRec kmodl
  (kctx'', tctx') <- typeModule kctx' tctx kmodl
  checkNoVarsInSessionPatterns kmodl
  pure (sctx', kctx'', tctx', kmodl)

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
                (sctx, kctx, tctx, kmodl) <- validateModule emptyScopingCtx emptyKindCtx emptyTypeCtx (mconcat modules)
                vs                        <- get
                pure (srcs, vs, sctx, kctx, tctx, kmodl)
      of Left es -> do
          printErrors srcs es
          putStrLn failedToLoadModule
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
    Left _  -> Nothing <$ putStrLn (notASourceFile path)
    Right s -> pure (Just s)
