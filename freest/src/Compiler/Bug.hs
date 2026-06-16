{- |
Module      :  Compiler.Bug
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Marker for impossible states inside the compiler: paths that should
never be reached if the surrounding invariants hold. Distinct from
'UI.Error', which reports user-facing diagnostics.
-}
module Compiler.Bug ( internalError ) where

import GHC.Stack ( HasCallStack, SrcLoc(..), callStack, getCallStack )

-- | Abort with an "(Internal error) " prefix to flag a compiler bug.
--
-- The call site is recovered from the 'HasCallStack' implicit parameter,
-- so callers do not pass it explicitly — the GHC compiler stamps the
-- module, file and line at every solve of the constraint.
internalError :: HasCallStack => String -> a
internalError msg = error $ "(Internal error) " ++ location ++ ": " ++ msg
  where
    location = case getCallStack callStack of
      (_, loc) : _ -> srcLocModule loc ++ ":" ++ show (srcLocStartLine loc)
      []           -> "<unknown>"
