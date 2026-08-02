{- |
Module      :  Compiler.Bug
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Marker for impossible states inside the compiler: paths that should
never be reached if the surrounding invariants hold. Distinct from
'UI.Error', which reports user-facing diagnostics.

Also the reporting end: 'handleBug' turns such a failure — and any other
unforeseen exception — into a report the user can act on.
-}
module Compiler.Bug ( internalError, handleBug, reportBug ) where

import Paths_freest qualified as Paths

import Control.Exception
  ( AsyncException, Exception(..), SomeException, catch, fromException, throwIO )
import Data.Version ( showVersion )
import GHC.Stack ( HasCallStack, SrcLoc(..), callStack, getCallStack )
import System.Exit ( ExitCode, exitFailure )
import System.IO ( hPutStrLn, stderr )

-- | Abort with a compiler bug.
--
-- The call site is recovered from the 'HasCallStack' implicit parameter,
-- so callers do not pass it explicitly — the GHC compiler stamps the
-- module, file and line at every solve of the constraint.
internalError :: HasCallStack => String -> a
internalError msg = error (location ++ ": " ++ msg)
  where
    location = case getCallStack callStack of
      (_, loc) : _ -> srcLocModule loc ++ ":" ++ show (srcLocStartLine loc)
      []           -> "<unknown>"

-- | Run a compiler action, reporting any bug it hits and giving up.
handleBug :: Maybe FilePath -> IO a -> IO a
handleBug source act = catch act \e -> reportBug source e >> exitFailure

-- | Report an exception as a compiler bug. A deliberate exit and an interrupt
-- are no such thing, and are passed on untouched.
reportBug :: Maybe FilePath -> SomeException -> IO ()
reportBug source e
  | Just code <- fromException e = throwIO (code :: ExitCode)
  | Just intr <- fromException e = throwIO (intr :: AsyncException)
  | otherwise = hPutStrLn stderr (report source (displayException e))
  where
  report source body = unlines $
    [ "freest: internal compiler error"
    , ""
    ]
    ++ map ("  " ++) (lines body) ++
    [ ""
    , "  version: " ++ showVersion Paths.version
    ]
    ++ [ "  while compiling: " ++ path | Just path <- [source] ] ++
    [ ""
    , "Please report this, quoting the program and the text above:"
    , "  https://github.com/freest-lang/freest/issues"
    , "  freest-lang@listas.ciencias.ulisboa.pt"
    ]
