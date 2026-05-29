module ArrowMultiplicityMismatch where

foo : (Int -1-> Int) -> Int
foo f = f 0

main = foo (\(x : Int) -> x)