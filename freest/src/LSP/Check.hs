module LSP.Check (checkForErrors) where

-- LSP

import Compiler.Include (IncludeError (..))
import Compiler.Pipeline (LoadState, loadPreludeAndModuleWithErrors)
import Data.Text (pack)
import LSP.Util (buildDiagnostic, originRange)
import GHC.IO (unsafePerformIO)
import LSP.Translate (errorTypeToDiagnostic)
import Language.LSP.Protocol.Types qualified as LSP
import UI.CLI (defaultRunOpts, filePath, notASourceFile)

checkForErrors :: FilePath -> Either [LSP.Diagnostic] LoadState
checkForErrors = unsafePerformIO . checkForParseErrors

checkForParseErrors :: FilePath -> IO (Either [LSP.Diagnostic] LoadState)
checkForParseErrors filePath = do
  let runOpts = defaultRunOpts {filePath = Just filePath}

  parsedModule <- loadPreludeAndModuleWithErrors filePath

  case parsedModule of
    Left (InvalidRoot p) ->
      pure $ Left [buildDiagnostic (notASourceFile p) originRange]
    Left (GraphErrors source errors) ->
      pure $ Left $ map (errorTypeToDiagnostic source runOpts) errors
    Right state -> do
      pure (Right state)
