{- |
Module      :  Load
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Loading FreeST source files: parsing, scoping, kinding and typing,
with or without the implicit Prelude. On success returns the scoped
module; on failure prints the errors and returns 'Nothing'.
-}
module Load
  ( loadPrelude
  , loadModule
  , loadPreludeAndModule
  , loadNoModule
  ) where

import Syntax.Module qualified as M
import Parser.Parser ( runParseModule )
import Parser.Scoping ( scopeModule', emptyScopingCtx, ScopingCtx )
import Validation.Base ( ValidationState, emptyValidationState, runValidation )
import Validation.Kinding ( kindModule )
import Validation.Typing ( typeModule, TypeCtx )
import UI.CLI ( preludePath, moduleLoaded, noModuleLoaded, preludeNotLoaded, failedToLoadModule, notASourceFile )
import UI.Error ( printErrors, Error )
import Paths_freest ( getDataFileName )

import Control.Exception ( IOException, try )
import Control.Monad.State ( get )
import Data.Map qualified as Map

-- | Load a program module on its own (no Prelude). Returns the scoped
-- module after successful kinding and typing, or 'Nothing' if errors
-- were found (in which case they are printed).
loadModule :: FilePath -> IO (Maybe (ValidationState, ScopingCtx, TypeCtx, M.ScopedModule))
loadModule fp = putStrLn preludeNotLoaded >> loadM moduleLoaded fp

-- | Load just the Prelude.
loadPrelude :: IO (Maybe (ValidationState, ScopingCtx, TypeCtx, M.ScopedModule))
loadPrelude = getDataFileName preludePath >>= loadM noModuleLoaded

-- | Load no module at all, just print a message to that effect,
-- thus centralising all module loading messages in this module.
loadNoModule :: IO ()
loadNoModule = putStrLn preludeNotLoaded >> putStrLn noModuleLoaded
  
-- | Load a program module on its own or else the Prelude. Returns the scoped
-- module after successful kinding and typing, or 'Nothing' if errors
-- were found (in which case they are printed).
loadM :: String -> FilePath -> IO (Maybe (ValidationState, ScopingCtx, TypeCtx, M.ScopedModule))
loadM moduleMessage programPath = tryRead programPath >>= \case
  Nothing -> pure Nothing -- notASourceFile already printed
  Just programSrc ->
    case  -- Parse the program, then scope, kind and type it.
      do  programModule <- runParseModule programPath programSrc
          runValidation emptyValidationState do
            (scopeCtx, scopedModule) <- scopeModule' emptyScopingCtx programModule
            kmodl <- kindModule scopedModule
            (_, typeCtx)      <- typeModule kmodl
            vs <- get
            pure (vs, scopeCtx, typeCtx, scopedModule)
      of Left es -> do
          printSourceErrors [(programPath, programSrc)] es
          putStrLn failedToLoadModule
          pure Nothing
         Right result -> do
          putStrLn moduleMessage
          pure (Just result)

-- | Load a program module joined with the Prelude. Returns the scoped
-- composed module after successful kinding and typing, or 'Nothing' if
-- errors were found (in which case they are printed).
loadPreludeAndModule :: FilePath -> IO (Maybe (ValidationState, ScopingCtx, TypeCtx, M.ScopedModule))
loadPreludeAndModule programPath = do
  preludeFile <- getDataFileName preludePath
  mPreludeSrc <- tryRead preludeFile
  mProgramSrc <- tryRead programPath
  case (mPreludeSrc, mProgramSrc) of
    (Just preludeSrc, Just programSrc) ->
      case  -- Parse the Prelude and the program, join them in a single
            -- module, then scope, kind and type it.
        do  preludeModule <- runParseModule preludePath preludeSrc
            programModule <- runParseModule programPath programSrc
            let composedModule = mappend preludeModule programModule
            runValidation emptyValidationState do
              (scopeCtx, scopedModule) <- scopeModule' emptyScopingCtx composedModule
              kinded <- kindModule scopedModule
              (_, typeCtx) <- typeModule kinded
              vs <- get
              pure (vs, scopeCtx, typeCtx, scopedModule)
        of Left es -> do
            printSourceErrors [ (preludePath, preludeSrc)
                              , (programPath, programSrc)
                              ] es
            putStrLn failedToLoadModule
            pure Nothing
           Right result -> do
            putStrLn moduleLoaded
            pure (Just result)
    _ -> pure Nothing -- notASourceFile already printed for missing file(s)

-- | Try to read a file; on IO failure print 'notASourceFile' and return
-- 'Nothing', otherwise return the file contents wrapped in 'Just'.
tryRead :: FilePath -> IO (Maybe String)
tryRead path = do
  result <- try (readFile path) :: IO (Either IOException String)
  case result of
    Left _  -> Nothing <$ putStrLn (notASourceFile path)
    Right s -> pure (Just s)

-- | Print the given errors, keyed by their source file.
printSourceErrors :: [(FilePath, String)] -> [Error] -> IO ()
printSourceErrors srcs = printErrors (Map.fromList (map (fmap lines) srcs))
