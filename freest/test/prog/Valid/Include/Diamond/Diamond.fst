{-# INCLUDE "A.fst" #-}
{-# INCLUDE "B.fst" #-}
module Diamond where

-- A and B both INCLUDE Base; it must be merged exactly once, otherwise
-- 'base' is a duplicate definition and the module fails to load.
main : ()
main = print (fromA + fromB)
