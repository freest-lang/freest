module PolyLessArgs where

fst' : forall (a b : *T). (a, b) -> a
fst' @a @b (x1, x2) = x1

main : Int
main = fst' @Int (2, True)

