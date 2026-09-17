-- LinId accepts the linear type pass applies g to.
type LinId (a : 1T) = a

pass : forall g -> g (Int -1-> Int) -> g (Int -1-> Int)
pass x = x

main : ()
main = let f = pass @LinId (\(x:Int) -1-> x) in print @Int (f 1)
