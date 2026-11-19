module LSP.Check (checkProgram) where

import Compiler.Include (IncludeError (..))
import Compiler.Pipeline (loadPreludeAndModuleWithErrors)
import Control.Exception (SomeAsyncException, SomeException, displayException, evaluate, fromException, handle, throwIO)
import Data.Map.Strict qualified as Map
import LSP.FreestLspM (DiagnosticReport)
import LSP.Translate (errorTypeToDiagnostic)
import LSP.Util (buildDiagnostic, originRange)
import Syntax.Base (Located (getSpan), Span (filepath))
import UI.CLI (defaultRunOpts, filePath, notASourceFile)
import UI.Error (Source)

-- | Diagnostics for every file the check read, possibly none, keyed by its path as written.
checkProgram :: Source -> FilePath -> IO DiagnosticReport
checkProgram openFiles path = handle reportCrash do
  diagnostics <- byFile <$> loadPreludeAndModuleWithErrors openFiles path
  forceDiagnostics diagnostics
  where
    byFile = \case
      Left (InvalidRoot p) ->
        Map.singleton path [buildDiagnostic (notASourceFile p) originRange]
      Left (GraphErrors source errors) ->
        Map.fromListWith (flip (++)) [(fileOf source e, [errorTypeToDiagnostic source runOpts e]) | e <- errors]
          `Map.union` filesRead source
      Right (source, _, _, _, _, _) -> filesRead source
    filesRead source = Map.insert path [] ([] <$ source)
    fileOf source e
      | filepath (getSpan e) `Map.member` source = filepath (getSpan e)
      | otherwise = path
    runOpts = defaultRunOpts {filePath = Just path}
    reportCrash (e :: SomeException)
      | Just (_ :: SomeAsyncException) <- fromException e = throwIO e
      | otherwise =
          pure $ Map.singleton path [buildDiagnostic ("internal compiler error\n" ++ displayException e) originRange]

-- | Build every diagnostic now, so that a compiler crash happens inside 'handle'.
forceDiagnostics :: DiagnosticReport -> IO DiagnosticReport
forceDiagnostics diagnostics = diagnostics <$ mapM_ evaluate (concat (Map.elems diagnostics))
