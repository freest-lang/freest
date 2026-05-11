module LinMultForallAppliedTwice where

foo : Int -> forall #m -1-> (Int -m-> Int) -> Int
foo x #m f = f x

main : Int
main = 
  let closure = foo 1
  in closure #* succ; closure #* succ