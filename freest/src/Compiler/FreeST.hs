-- |
-- Module      :  Compiler.FreeST
-- Copyright   :  © The FreeST Team
-- Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt
--
-- The entry point of the FreeST compiler.
module Compiler.FreeST (freest, runFreeST) where

import Compiler.Pipeline (LoadState, loadSilent)
import Compiler.REPL (ReplState (..), emptyReplState, repl)
import Control.Concurrent.MVar
import Control.Exception (catch)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.State
import Interpreter.Eval (evalModule)
import Interpreter.Exception (printException)
import Interpreter.Value (emptyValueCtx)
import LSP.FreestLspM (FreestLspM)
import LSP.Handler (handlers)
import Language.LSP.Server
import Options.Applicative (execParser)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import UI.CLI (RunOpts (..), noModuleLoaded, opts, version)

-- | The entry point of the FreeST compiler. Parses the command line options
-- and runs the compiler pipeline or else calls the REPL.
freest :: IO ()
freest = execParser opts >>= runFreeST

-- | Dispatch on the parsed command line options.
runFreeST :: RunOpts -> IO ()
runFreeST RunOpts {languageServer = True} =
  hPutStrLn stderr "FreeST LSP server connected."
    >> newMVar Nothing
    >>= \state ->
      void $
        runServer $
          ServerDefinition
            { onConfigurationChange = const $ pure $ Right (),
              doInitialize = \env _req -> pure $ Right env,
              staticHandlers = handlers,
              interpretHandler = \env -> Iso (forward env state) liftIO,
              options = defaultOptions
            }
  where
    forward :: LanguageContextEnv config -> MVar (Maybe LoadState) -> FreestLspM config a -> IO a
    forward env state m =
      modifyMVar state \oldState ->
        runLspT env $ runStateT m oldState >>= \(e, newState) -> return (newState, e)
runFreeST RunOpts {interactive = True, filePath = mPath, implicitPrelude = ip} =
  repl emptyReplState {filePath = mPath, implicitPrelude = ip}
runFreeST RunOpts {filePath = Nothing} =
  putStrLn (version ++ "\n" ++ noModuleLoaded)
    >> exitSuccess
runFreeST RunOpts {filePath = Just programPath, implicitPrelude = ip} =
  loadSilent ip programPath >>= \case
    Nothing -> exitFailure
    Just (src, _, _, _, _, modl) ->
      catch
        (evalModule emptyValueCtx modl >> exitSuccess)
        (\e -> printException src e >> exitFailure)
