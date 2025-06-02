module PolySUTL where

id' : forall (a : 1T). a -> a
id' @a x = x

f : Int 1-> Int
f x = 2 * x

main : Int
main =
  (id' @(Int 1-> Int) f) 5
