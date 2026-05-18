{- |
Module      :  FreeSTi
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST interactive interpreter (REPL).
-}
module FreeSTi ( main ) where

import Load
import REPL ( ReplState(..), emptyReplState, repl )
import Syntax.Module
import UI.CLI ( RunOpts(..), opts )

import Options.Applicative ( execParser )

-- | The entry point of the FreeSTi interpreter. Parses the command line options
-- and passes them to the FreeSTi interpreter.
main :: IO ()
main = execParser opts >>= freesti

-- | The FreeSTi interpreter.
freesti :: RunOpts -> IO ()
freesti RunOpts{filePath = Nothing,          implicitPrelude = False} =
  replWith False Nothing Nothing
freesti RunOpts{filePath = Nothing,          implicitPrelude = True}  =
  loadPrelude                  >>= replWith True  Nothing
freesti RunOpts{filePath = Just programPath, implicitPrelude = False} =
  loadModule programPath       >>= replWith False (Just programPath)
freesti RunOpts{filePath = Just programPath, implicitPrelude = True}  =
  loadPreludeAndModule programPath >>= \case
    Just scoped ->                 replWith True (Just programPath) (Just scoped)
    Nothing     -> loadPrelude >>= replWith True (Just programPath)
    -- TODO: the module is not loaded when Prelude loading fails.

-- | Enter the REPL with the loaded module (if any), preserving the file path
-- and implicit-prelude flag even when the load failed (errors were already printed).
replWith :: Bool -> Maybe FilePath -> Maybe ScopedModule -> IO ()
replWith ip mPath mScoped = repl $ case mScoped of
  Nothing     -> base
  Just scoped -> base{modl = scoped}
  where
    base :: ReplState
    base = emptyReplState{implicitPrelude = ip, filePath = mPath}
