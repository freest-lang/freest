module Dot where

dot : forall (a : 1T) (b : 1T) (c : 1T) -> (b -> c) -> (a -> b) -> a -> c
dot @a @b @c f g x = f (g x)

double : Int -> Int
double x = 2 * x

isZero : Int -> Bool
isZero x = x == 0

main : ()
main = print (dot isZero double 7)
