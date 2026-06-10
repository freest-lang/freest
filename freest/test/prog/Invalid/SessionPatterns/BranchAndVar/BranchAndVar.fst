module BranchAndVar where

f : &{L: Skip} -> Skip
f (&L c) = c
f c = case c of
  &L c' -> c'