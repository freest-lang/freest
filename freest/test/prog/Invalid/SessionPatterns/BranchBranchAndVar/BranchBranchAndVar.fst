module BranchAndVar where

type U, T : 1C
type U = &{C: Wait, D: Wait}
type T = &{A: U, B: U}

f : T -> ()
f (&A (&C Wait)) = ()
f (&B (&C Wait)) = ()
f (&A (&D Wait)) = ()
f (&B c) =
  case c of
    &D c' -> wait c'