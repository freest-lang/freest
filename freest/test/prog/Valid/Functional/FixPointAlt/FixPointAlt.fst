module FixPointAlt where

-- The fixed-point Z combinator: Z=\f.(\x.f(\z.xxz))(\y.f(\z.yyz)) is
-- used to calculate the factorial of 8

-- This is the Y-combinator. It never halts in a strict language
-- fix' : forall a  -> ((a -> a) -> (a -> a)) -> (a -> a)
-- fix' f = f (fix' @a f) 

fix' : forall (a : *T) -> ((a -> a) -> (a -> a)) -> a -> a
fix' @a f x = f (fix' f) x

fact : Int -> Int
fact = fix' (\f -> (\n ->
  if n == 0 then 1 else n * f (n - 1)))

main : ()
main = print (fact 5)