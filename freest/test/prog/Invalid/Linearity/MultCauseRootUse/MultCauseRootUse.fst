-- f reaches useLin through pipe, so the linear requirement must be blamed on
-- useLin's argument, not on the call that carried it there.
k : forall #m -> Int -> Int -m-> Int
k #m x y = x + y

pipe : forall #n -> (Int -n-> Int) -> (Int -n-> Int)
pipe #n f = f

useLin : (Int -1-> Int) -> Int
useLin f = f 2

main : ()
main = let f = k 1 in let g = pipe f in print @Int (useLin g + f 3)
