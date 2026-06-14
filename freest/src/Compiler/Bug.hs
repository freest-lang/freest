{- |
Module      :  Compiler.Bug
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Marker for impossible states inside the compiler: paths that should
never be reached if the surrounding invariants hold. Distinct from
'UI.Error', which reports user-facing diagnostics.
-}
module Compiler.Bug ( internalError ) where

import GHC.Stack ( HasCallStack )

-- | Abort with a "(Internal error) " prefix to flag a compiler bug.
-- The first argument names the offending site (e.g. @"Module.function"@)
-- and prefixes the message so the call site is visible without a stack trace.
internalError :: HasCallStack => String -> String -> a
internalError loc msg = error $ "(Internal error) " ++ loc ++ ": " ++ msg
