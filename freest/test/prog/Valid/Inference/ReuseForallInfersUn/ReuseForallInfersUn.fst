-- As Valid/Inference/ReuseInfersUn, with the free multiplicity on a
-- `forall (a : *T)` rather than an arrow: using `f` twice bounds it, so it
-- comes out `*`.
k : forall #m -> Int -> forall (a : *T) -m-> a -> Int
k #m x @a y = x

main : ()
main = let f = k 1 in print @Int (f 2 + f True)
