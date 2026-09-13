-- Instantiating `#m` reaches the multiplicity of a `forall (a : *T)`, so
-- `k #* 1` is unrestricted and can be applied twice.
k : forall #m -> Int -> forall (a : *T) -m-> a -> Int
k #m x @a y = x

main : ()
main = let f = k #* 1 in print @Int (f 2 + f True)
