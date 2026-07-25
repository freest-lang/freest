module LSP.Check (checkForErrors) where

-- LSP

import Compiler.Pipeline (LoadState, loadModule, loadPrelude, loadPreludeAndModule, loadPreludeAndModuleWithErrors)
import GHC.IO (unsafePerformIO)
import LSP.Translate (errorTypeToDiagnostic)
import Language.LSP.Protocol.Types qualified as LSP
import Paths_freest (getDataFileName)
import UI.CLI (defaultRunOpts, filePath, preludePath)

checkForErrors :: FilePath -> Either [LSP.Diagnostic] LoadState
checkForErrors = unsafePerformIO . checkForParseErrors

checkForParseErrors :: FilePath -> IO (Either [LSP.Diagnostic] LoadState)
checkForParseErrors filePath = do
  let runOpts = defaultRunOpts {filePath = Just filePath}

  parsedModule <- loadPreludeAndModuleWithErrors filePath

  case parsedModule of
    Left (source, errors) -> do
      pure $ Left $ map (errorTypeToDiagnostic source runOpts) errors
    Right state -> do
      pure (Right state)
