module PolyMoreArgs where

id' : forall (a : *T) -> a -> a
id' @a x = x

main : Int
main = id' @Int @Bool 5
