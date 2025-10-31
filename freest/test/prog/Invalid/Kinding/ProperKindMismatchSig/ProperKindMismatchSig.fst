module ProperKindMismatchSig where

type Box : 1T -> 1T
type Box a = a

x : Box
x = 42