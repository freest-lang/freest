{- |
Module      :  Compiler.FreeST
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST compiler.
-}
module Compiler.FreeST ( freest, runFreeST ) where

import Interpreter.Eval (evalModule)
import Interpreter.Value (emptyEnv)
import UI.CLI ( RunOpts(..), opts, version, noModuleLoaded )
import Compiler.REPL ( ReplState(..), emptyReplState, repl )
import Compiler.Pipeline ( loadSilent )

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
runFreeST RunOpts{filePath = Just programPath, implicitPrelude = ip} =
  loadSilent ip programPath >>= \case
    Nothing -> exitFailure
    Just (_, _, _, _, _, modl) -> evalModule emptyEnv modl >> exitSuccess
