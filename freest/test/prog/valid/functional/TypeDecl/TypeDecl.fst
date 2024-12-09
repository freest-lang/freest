module TypeDecl where

type T : *T
type T = U

type U : *T
type U = Int

main : T
main = 5
