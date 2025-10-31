module ExpectsTooManyArgsLambda where

foo : Int -> Int -> Int
foo _ = \(x : Int) (y : Int) -> 0