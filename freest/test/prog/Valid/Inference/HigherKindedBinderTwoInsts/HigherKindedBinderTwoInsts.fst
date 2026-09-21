-- g is instantiated at two kinds neither of which is below the other. The
-- binder takes the join of what they require, which is where writing
-- `(g : *T -> 1T)` by hand lands: fixing it at either argument would reject
-- the other, and inference may not be stronger than annotation.
type UnId  (a : *T) = a
type LinId (a : 1T) = a

pass : forall g -> g (Int -> Int) -> g (Int -> Int)
pass x = x

main : ()
main = let f = pass @UnId  (\(x:Int) -> x) in
       let h = pass @LinId (\(y:Int) -> y) in
       print @Int (f 1 + h 2)
