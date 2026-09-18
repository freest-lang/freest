-- pass never applies g to a linear type, so g's parameter may be unrestricted
-- and UnId is accepted.
type UnId (a : *T) = a

pass : forall g -> g (Int -> Int) -> g (Int -> Int)
pass x = x

main : ()
main = let f = pass @UnId (\(x:Int) -> x) in print @Int (f 1 + f 2)
