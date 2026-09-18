-- g's parameter in pass2 is bounded only by pass's, which is itself unrestricted.
type UnId (a : *T) = a

pass : forall g -> g (Int -> Int) -> g (Int -> Int)
pass x = x

pass2 : forall g -> g (Int -> Int) -> g (Int -> Int)
pass2 @g x = pass @g x

main : ()
main = let f = pass2 @UnId (\(x:Int) -> x) in print @Int (f 1 + f 2)
