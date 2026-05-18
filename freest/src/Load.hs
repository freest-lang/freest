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
  ) where

import Syntax.Module qualified as M
import Parser.Parser ( runParseModule )
import Parser.Scoping ( scopeModule, emptyScopingCtx )
import Validation.Base ( emptyValidationState, runValidation )
import Validation.Kinding ( kindModule )
import Validation.Typing ( typeModule )
import UI.CLI ( preludePath, moduleLoaded, noModuleLoaded,failedToLoadModule )
import UI.Error ( printErrors, Error )
import Paths_freest ( getDataFileName )

import Data.Map qualified as Map

-- | Load a program module on its own (no Prelude). Returns the scoped
-- module after successful kinding and typing, or 'Nothing' if errors
-- were found (in which case they are printed).
loadModule :: FilePath -> IO (Maybe M.ScopedModule)
loadModule = loadM moduleLoaded

-- | Load just the Prelude.
loadPrelude :: IO (Maybe M.ScopedModule)
loadPrelude = getDataFileName preludePath >>= loadM noModuleLoaded

-- | Load a program module on its own or else the Prelude. Returns the scoped
-- module after successful kinding and typing, or 'Nothing' if errors
-- were found (in which case they are printed).
loadM :: String -> FilePath -> IO (Maybe M.ScopedModule)
loadM moduleMessage programPath = do
  programSrc <- readFile programPath
  case  -- Parse the program, then scope, kind and type it.
    do  programModule <- runParseModule programPath programSrc
        runValidation emptyValidationState do
          scoped <- scopeModule emptyScopingCtx programModule
          kinded <- kindModule scoped
          _      <- typeModule kinded
          pure scoped
    of Left es -> do
        printSourceErrors [(programPath, programSrc)] es
        putStrLn failedToLoadModule
        pure Nothing
       Right scoped -> do
        putStrLn moduleMessage
        pure (Just scoped)

-- | Load a program module joined with the Prelude. Returns the scoped
-- composed module after successful kinding and typing, or 'Nothing' if
-- errors were found (in which case they are printed).
loadPreludeAndModule :: FilePath -> IO (Maybe M.ScopedModule)
loadPreludeAndModule programPath = do
  preludeSrc <- getDataFileName preludePath >>= readFile
  programSrc <- readFile programPath
  case  -- Parse the Prelude and the program, join them in a single
        -- module, then scope, kind and type it.
    do  preludeModule <- runParseModule preludePath preludeSrc
        programModule <- runParseModule programPath programSrc
        let composedModule = mappend preludeModule programModule
        runValidation emptyValidationState do
          scoped <- scopeModule emptyScopingCtx composedModule
          kinded <- kindModule scoped
          _      <- typeModule kinded
          pure scoped
    of Left es -> do
        printSourceErrors [ (preludePath, preludeSrc)
                          , (programPath, programSrc)
                          ] es
        putStrLn failedToLoadModule
        pure Nothing
       Right scoped -> do
        putStrLn moduleLoaded
        pure (Just scoped)

-- | Print the given errors, keyed by their source file.
printSourceErrors :: [(FilePath, String)] -> [Error] -> IO ()
printSourceErrors srcs = printErrors (Map.fromList (map (fmap lines) srcs))
