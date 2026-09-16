-- f's multiplicity is left open by k 1; useLin fixes it at 1, so f cannot be
-- used again.
k : forall #m -> Int -> Int -m-> Int
k #m x y = x + y

useLin : (Int -1-> Int) -> Int
useLin f = f 2

main : ()
main = let f = k 1 in print @Int (useLin f + f 3)
