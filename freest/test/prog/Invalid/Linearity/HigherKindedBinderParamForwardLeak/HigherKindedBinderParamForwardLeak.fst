-- pass applies g to a linear type; pass2 forwards g to it, so UnId must be
-- rejected at pass2 too.
type UnId (a : *T) = a

pass : forall g -> g (Int -> Int) -> g (Int -1-> Int) -> g (Int -> Int)
pass x _ = x

pass2 : forall g -> g (Int -> Int) -> g (Int -1-> Int) -> g (Int -> Int)
pass2 @g x y = pass @g x y

main : ()
main = let f = pass2 @UnId (\(x:Int) -> x) (\(x:Int) -1-> x) in print @Int (f 1 + f 2)
