{- |
Module      :  FreeST
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST compiler.
-}
module FreeST ( main, freest ) where

import Load ( loadModule, loadPreludeAndModule )
import UI.CLI ( RunOpts(..), opts, version, noModuleLoaded )

import Options.Applicative ( execParser )
import System.Exit ( exitSuccess, exitFailure )

-- | The entry point of the FreeST compiler. Parses the command line options
-- and passes them to the compiler pipeline.
main :: IO ()
main = do
  execParser opts >>= freest

-- | The FreeST compiler pipeline.
freest :: RunOpts -> IO ()
freest RunOpts{filePath = Nothing} =
  putStrLn (version ++ "\n" ++ noModuleLoaded) >>
  exitSuccess
freest RunOpts{filePath = Just programPath, implicitPrelude = False} =
  loadModule programPath >>=
  maybe exitFailure (const exitSuccess)
freest RunOpts{filePath = Just programPath, implicitPrelude = True} =
  loadPreludeAndModule programPath >>=
  maybe exitFailure (const exitSuccess)
