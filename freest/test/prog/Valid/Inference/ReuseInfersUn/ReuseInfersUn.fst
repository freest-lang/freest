-- Nothing in the application says what `#m` is. Using `f` twice is what settles
-- it: the usage rules bound the arrow's multiplicity, so it comes out `*`
-- rather than taking the default and making `f` linear.
k : forall #m -> Int -> Int -m-> Int
k #m x y = x + y

main : ()
main = let f = k 1 in print @Int (f 2 + f 3)
