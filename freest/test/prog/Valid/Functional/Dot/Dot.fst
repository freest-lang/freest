module Dot where

dot : forall (a b c : 1T). (b -> c) -> (a -> b) -> a -> c
dot @a @b @c f g x = f (g x)

double : Int -> Int
double x = 2 * x

isZero : Int -> Bool
isZero x = x == 0

main : Bool
main = dot  @Int @Int @Bool isZero double 7

