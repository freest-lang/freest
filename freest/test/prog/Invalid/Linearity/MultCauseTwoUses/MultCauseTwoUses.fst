-- Two uses fix k's #m in opposite directions; each cause must name its own use,
-- not repeat the span the error already points at.
k : forall #m -> Int -> Int -m-> Int
k #m x y = x + y

useLin : (Int -1-> Int) -> Int
useLin f = f 2

twice : forall #n -> (Int -n-> Int) -> Int
twice #n g = g 1 + g 2

main : ()
main = let f = k 1 in print @Int (useLin f + twice f)
