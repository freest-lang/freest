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
import Compiler.REPL ( ReplState(..), emptyReplState, repl )
import Compiler.Pipeline ( loadSilent )
import Compiler.Bug ( handleBug )
import Interpreter.Exception ( printException )

import Control.Exception ( catch )
import Options.Applicative ( execParser )
import System.Environment ( withArgs, withProgName )
import System.Exit ( exitSuccess, exitFailure )

-- | The entry point of the FreeST compiler. Parses the command line options
-- and runs the compiler pipeline or else calls the REPL.
freest :: IO ()
freest = execParser opts >>= runFreeST

-- | Dispatch on the parsed command line options.
runFreeST :: RunOpts -> IO ()
runFreeST RunOpts{interactive = True, filePath = mPath, implicitPrelude = ip, progArgs = args} =
  handleBug mPath (withArgs args (repl emptyReplState{filePath = mPath, implicitPrelude = ip}))
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
      | otherwise -> catch (asProgram (evalModule emptyValueCtx modl) >> exitSuccess)
                           (\e -> printException src e >> exitFailure)
      where asProgram = withProgName programPath . withArgs args
