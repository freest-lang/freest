-- A free multiplicity variable in a signature is quantified implicitly.
app : (Int -m-> Int) -> Int -m-> Int
app f x = f x

main : ()
main = print (app #1 (\y -1-> y + 1) 1 + app succ 1)
