-- `cap`'s binder is left to inference, and inside the body the capture rule
-- bounds it by the rigid `#m`. Instantiating that binder at a linear type here
-- must stay a fact about this call: written into the kind solution it would pin
-- the binder variable the signature shares with every other use, leaving the
-- unsatisfiable `1 <: m` against a rigid `m`.
cap : forall #m a -> a -> (a -1-> ()) -m-> ()
cap #m @a x k = k x

sink : (Int -1-> Int) -1-> ()
sink g = print @Int (g 1)

main : ()
main = cap (\(x:Int) -1-> x) sink
