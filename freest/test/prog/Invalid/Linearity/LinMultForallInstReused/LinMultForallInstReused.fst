-- The argument pins `#m` to `1`, so reuse cannot relax it: `f` is linear and
-- using it twice is an error. The companion of Valid/Inference/ReuseForallInfersUn.
k : forall #m -> (Int -m-> Int) -> forall (a : *T) -m-> a -m-> Int
k #m g @a y = g 1

main : ()
main = let f = k (\(x:Int) -1-> x) in print @Int (f 2 + f True)
