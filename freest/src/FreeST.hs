{- |
Module      :  FreeST
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST compiler.
-}
module FreeST ( freest, runFreeST ) where

import UI.CLI ( RunOpts(..), opts, version, noModuleLoaded )
import REPL ( ReplState(..), emptyReplState, repl )
import Pipeline ( loadModule, loadPreludeAndModule )

import Options.Applicative ( execParser )
import System.Exit ( exitSuccess, exitFailure )

-- | The entry point of the FreeST compiler. Parses the command line options
-- and runs the compiler pipeline or else calls the REPL.
freest :: IO ()
freest = execParser opts >>= runFreeST

-- | Dispatch on the parsed command line options.
runFreeST :: RunOpts -> IO ()
runFreeST RunOpts{interactive = True, filePath = mPath, implicitPrelude = ip} =
  repl emptyReplState{filePath = mPath, implicitPrelude = ip}
runFreeST RunOpts{filePath = Nothing} =
  putStrLn (version ++ "\n" ++ noModuleLoaded) >>
  exitSuccess
runFreeST RunOpts{filePath = Just programPath, implicitPrelude = False} =
  loadModule programPath >>=
  maybe exitFailure (const exitSuccess)
runFreeST RunOpts{filePath = Just programPath, implicitPrelude = True} =
  loadPreludeAndModule programPath >>=
  maybe exitFailure (const exitSuccess)
