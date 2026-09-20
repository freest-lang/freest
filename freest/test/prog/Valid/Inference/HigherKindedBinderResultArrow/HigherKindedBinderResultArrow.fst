-- g's *result* is where the multiplicity matters here: `x` is used twice, so
-- `g (Int -> Int)` must come out unrestricted. The parameter-side least
-- solution is what makes `@UnId` give it that.
type UnId (a : *T) = a

twice : forall g -> (g (Int -> Int) -> Int) -> g (Int -> Int) -> Int
twice k x = k x + k x

main : ()
main = print @Int (twice @UnId (\(f:Int -> Int) -> f 1) (\(x:Int) -> x))
