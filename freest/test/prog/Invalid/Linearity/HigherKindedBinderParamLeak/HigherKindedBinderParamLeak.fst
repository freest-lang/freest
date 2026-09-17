-- UnId's parameter must be unrestricted, but pass applies g to a linear type;
-- instantiating g at UnId would let f be used twice.
type UnId (a : *T) = a

pass : forall g -> g (Int -1-> Int) -> g (Int -1-> Int)
pass x = x

main : ()
main = let f = pass @UnId (\(x:Int) -1-> x) in print @Int (f 1 + f 2)
