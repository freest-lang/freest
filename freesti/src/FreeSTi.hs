{- |
Module      :  FreeSTi
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST interactive interpreter (REPL).
-}
module FreeSTi ( main ) where

import REPL ( ReplState(..), emptyReplState, repl )
import UI.CLI ( RunOpts(..), opts )

import Options.Applicative ( execParser )

-- | The entry point of the FreeSTi interpreter. Parses the command line options
-- and passes them to the FreeSTi interpreter.
main :: IO ()
main = execParser opts >>= freesti

-- | The FreeSTi interpreter. Seeds the REPL state from the command-line
-- options; module loading and the banner are handled by 'REPL.ini'.
freesti :: RunOpts -> IO ()
freesti RunOpts{filePath = mPath, implicitPrelude = ip} =
  repl $ emptyReplState{filePath = mPath,implicitPrelude = ip}
