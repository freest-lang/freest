module FixZCombinator where 

-- The fixed-point Z combinator: Z=\f.(\x.f(\z.xxz))(\y.f(\z.yyz)) is
-- used to calculate the factorial of 8

type X : *T -> *T
type X a = (X a) -> a -> a

fixZcomb : forall (a : *T). ((a -> a) -> (a -> a)) -> (a -> a)
fixZcomb @a f =
  (\(x : X a) -> f (\(z : a) -> x x z))
  (\(x : X a) -> f (\(z : a) -> x x z))

fact : Int -> Int
fact = fixZcomb (\(f : Int -> Int) -> (\(n : Int) ->
  if n == 0 then 1 else n * f (n - 1)))

main : Int
main = fact 8
