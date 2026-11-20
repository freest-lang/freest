-- `go`'s `m` is its function's, in scope through the binder `#m`, so it is not
-- quantified again and `go` takes no multiplicity argument.
f : forall #m -> (Int -m-> Int) -> Int
f #m g = go #m g 1
  where
    go : (Int -m-> Int) -> Int -m-> Int
    go h x = h x

main : ()
main = ()
