module ArrowMultMismatchLambdaN where

foo : (Int -> Int -1-> Int) -> Int
foo f = f 0 0

main = foo (\(x : Int) (y : Int) -> x)