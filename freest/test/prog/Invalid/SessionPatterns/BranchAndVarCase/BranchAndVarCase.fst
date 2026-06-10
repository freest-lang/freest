module BranchAndVarCase where

f : &{L: Skip} -> Skip
f c = case c of
  &L c' -> c'
  c'    -> case c' of
            &L c'' -> c''