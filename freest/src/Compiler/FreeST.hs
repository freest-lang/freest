{- |
Module      :  Compiler.FreeST
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST compiler.
-}
module Compiler.FreeST ( freest, runFreeST ) where

import Interpreter.Eval (evalModule)
import Interpreter.Value (emptyValueCtx)
import UI.CLI ( RunOpts(..), opts, version, noModuleLoaded )
import Compiler.REPL qualified as REPL
import Compiler.Pipeline ( loadSilent )
import Compiler.Bug ( handleBug )
import Interpreter.Exception ( printException, reportThreadFailure )

import LSP.FreestLspM ( DiagnosticReport, FreestLspM )
import LSP.Handler ( handlers, textDocumentSync )
import Language.LSP.Protocol.Types ( NormalizedUri )
import Language.LSP.Server

import Control.Concurrent.MVar
import Control.Exception ( catch )
import Control.Monad ( void )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.State ( runStateT )
import Data.Map.Strict ( Map )
import Data.Map.Strict qualified as Map
import System.IO ( hPutStrLn, stderr )
import GHC.Conc ( setUncaughtExceptionHandler )
import Options.Applicative ( execParser )
import System.Environment ( withArgs, withProgName )
import System.Exit ( exitSuccess, exitFailure )

-- | The entry point of the FreeST compiler. Parses the command line options
-- and runs the compiler pipeline or else calls the REPL.
freest :: IO ()
freest = execParser opts >>= runFreeST

-- | Dispatch on the parsed command line options.
runFreeST :: RunOpts -> IO ()
runFreeST RunOpts{languageServer = True} = do
  hPutStrLn stderr "FreeST LSP server connected."
  state <- newMVar Map.empty
  void $ runServer ServerDefinition
    { defaultConfig = ()
    , onConfigurationChange = const $ pure $ Right ()
    , doInitialize = \env _req -> pure $ Right env
    , staticHandlers = handlers
    , interpretHandler = \env -> Iso (forward env state) liftIO
    , options = defaultOptions { optTextDocumentSync = Just textDocumentSync }
    }
  where
    forward :: LanguageContextEnv config -> MVar (Map NormalizedUri DiagnosticReport) -> FreestLspM config a -> IO a
    forward env state m =
      modifyMVar state \old -> runLspT env $ (\(a, new) -> (new, a)) <$> runStateT m old
runFreeST RunOpts{interactive = True, filePath = mPath, implicitPrelude = ip, progArgs = args} =
  handleBug mPath (withArgs args (REPL.repl REPL.emptyReplState{REPL.filePath = mPath, REPL.implicitPrelude = ip}))
runFreeST RunOpts{filePath = Nothing} =
  putStrLn (version ++ "\n" ++ noModuleLoaded) >>
  exitSuccess
runFreeST RunOpts{filePath = Just programPath, implicitPrelude = ip, typecheckOnly = tc, progArgs = args} =
  handleBug (Just programPath) $
  loadSilent ip programPath >>= \case
    Nothing -> exitFailure
    Just (src, _, _, _, _, modl)
      | tc        -> exitSuccess
      -- the program sees its own arguments and name, not the compiler's
      | otherwise -> do
          setUncaughtExceptionHandler (reportThreadFailure (Just programPath) src)
          catch (asProgram (evalModule emptyValueCtx modl) >> exitSuccess)
                (\e -> printException src e >> exitFailure)
      where asProgram = withProgName programPath . withArgs args
