module BranchBranchAndVarCase where

type U, T : 1C
type U = &{C: Wait, D: Wait}
type T = &{A: U, B: U}

f : T -> ()
f c = case c of
  &A (&C Wait) -> ()
  &B (&C Wait) -> ()
  &A (&D Wait) -> ()
  c' -> case c' of
          &B c'' -> case c'' of
                    &D c''' -> wait c'''
