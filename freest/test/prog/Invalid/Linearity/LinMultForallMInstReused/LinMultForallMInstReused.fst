-- The argument pins `#m` to `1`, so reuse cannot relax it: `f` is linear and
-- using it twice is an error. The companion of Valid/Inference/ReuseForallMInfersUn.
k : forall #m -> (Int -m-> Int) -> forall #n -m-> Int -m+n-> Int
k #m g #n y = g y

main : ()
main = let f = k (\(x:Int) -1-> x) in print @Int (f 2 + f 3)
