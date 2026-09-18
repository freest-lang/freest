-- The error is at a use of g, not at an application, and the two multiplicities
-- come from the linear lambda and from the second use.
mk : forall #m -> (Int -m-> Int) -> (Int -m-> Int)
mk #m f = f

main : ()
main = let g = mk (\(x:Int) -1-> x) in
       let _ = g 1 in
       print @Int (g 2)
