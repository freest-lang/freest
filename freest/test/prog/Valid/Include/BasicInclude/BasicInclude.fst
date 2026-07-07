{-# INCLUDE "Helper.fst" #-}
module BasicInclude where

-- Definitions from the INCLUDEd Helper are in scope.
main : ()
main = print (double 21)
