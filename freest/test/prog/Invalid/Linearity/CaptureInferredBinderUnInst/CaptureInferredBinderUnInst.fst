-- The body bounds a's inferred kind by #m; this call instantiates #m at *.
cap : forall #m a -> a -> (a -1-> ()) -m-> ()
cap #m @a x k = k x

sink : (Int -1-> Int) -1-> ()
sink g = print @Int (g 1)

main : ()
main = let f = cap #* (\(x:Int) -1-> x) in f sink
