-- As Valid/Inference/ReuseInfersUn, with the free multiplicity on a `forall #n`
-- rather than an arrow: using `f` twice bounds it, so it comes out `*`.
k : forall #m -> Int -> forall #n -m-> Int -n-> Int
k #m x #n y = x + y

main : ()
main = let f = k 1 in print @Int (f 2 + f 3)
