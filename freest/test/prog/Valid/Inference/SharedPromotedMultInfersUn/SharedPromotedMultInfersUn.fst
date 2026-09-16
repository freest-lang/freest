-- f and g share the multiplicity two 1 leaves open; both uses need it unrestricted.
two : forall #m -> Int -> (Int -m-> Int, Int -m-> Int)
two #m x = (\y -m-> x + y, \y -m-> x - y)

useLin : (Int -1-> Int) -> Int
useLin f = f 2

useUn : (Int -> Int) -> Int
useUn f = f 3

main : ()
main = let (f, g) = two 1 in print @Int (useUn f + useUn g)
