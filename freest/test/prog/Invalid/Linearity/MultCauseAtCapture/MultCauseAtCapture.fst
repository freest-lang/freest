-- cap's #m is unrestricted because c is used twice, and linear because the
-- captured argument is; the causes must name those two places, not cap's
-- signature.
cap : forall #m a -> a -> (a -1-> ()) -m-> ()
cap #m @a x k = k x

main : ()
main = let c = cap @(Int -1-> Int) (\(x:Int) -1-> x) in
       let _ = c (\(f:Int -1-> Int) -1-> ()) in
       c (\(f:Int -1-> Int) -1-> ())
