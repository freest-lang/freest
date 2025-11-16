module DupConsChan where

type T : *T
data T = A | B

type C : 1S
type C = &{A: Skip, B: Skip}

main : T
main = A
