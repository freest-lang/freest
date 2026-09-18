-- The linear requirement comes from useLin, not from the composition that
-- produced the function it is applied to.
k : forall #m -> Int -> Int -m-> Int
k #m x y = x + y

comp : forall #m #n -> (Int -m+n-> Int) -> Int -m+n-> Int
comp #m #n g x = g x

useLin : (Int -1-> Int) -> Int
useLin f = f 1

main : ()
main = let f = k 1 in let g = f . k 2 in let h = comp g in print @Int (useLin h + g 1 + g 2)
