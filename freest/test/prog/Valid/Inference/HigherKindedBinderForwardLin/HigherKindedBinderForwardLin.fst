-- pass2's inferred binder is forwarded to pass's written `1T -> 1T`, and must
-- take its arrow kind from that call; `@LinId` then instantiates it.
type LinId (a : 1T) = a

pass : forall (g : 1T -> 1T) -> g (Int -> Int) -> g (Int -> Int)
pass x = x

pass2 : forall g -> g (Int -> Int) -> g (Int -> Int)
pass2 @g x = pass @g x

main : ()
main = let f = pass2 @LinId (\(x:Int) -> x) in print @Int (f 1)
