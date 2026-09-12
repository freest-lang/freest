-- The argument pins `#m` to `1`, so reuse cannot relax it: `f` is linear and
-- using it twice is an error. The companion of Valid/Inference/ReuseInfersUn.
k : forall #m -> (Int -m-> Int) -> Int -m-> Int
k #m g y = g y

main : ()
main = let f = k (\(x:Int) -1-> x) in print @Int (f 2 + f 3)
