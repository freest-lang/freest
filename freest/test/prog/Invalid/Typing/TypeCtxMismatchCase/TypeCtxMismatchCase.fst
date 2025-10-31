module TypeCtxMismatch where

type T : *T
data T = A | B | C

bar : T -> Close -> ()
bar x c = 
  case x of 
    A -> close c
    B -> ()
    C -> ()