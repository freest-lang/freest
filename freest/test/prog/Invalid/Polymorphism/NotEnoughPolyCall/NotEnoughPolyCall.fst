module NotEnoughPolyCall where

id' : forall (a : 1T). a -> a
id' @a c = c

main : Int
main = id' 5
