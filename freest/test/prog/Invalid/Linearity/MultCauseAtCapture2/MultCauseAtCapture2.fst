-- The unrestricted requirement comes from the clause that captures k under an
-- inferred closure, not from the #m parameter the closure's multiplicity names.
two : forall #m #n a -> a -> (a -> ()) -m-> (a -1-> ()) -n-> ()
two #m #n @a x k k2 = k2 x

sink : (Int -1-> Int) -1-> ()
sink g = print @Int (g 1)

k1 : (Int -1-> Int) -> ()
k1 g = print @Int (g 2)

main : ()
main = two #1 #1 (\(y:Int) -1-> y) k1 sink
