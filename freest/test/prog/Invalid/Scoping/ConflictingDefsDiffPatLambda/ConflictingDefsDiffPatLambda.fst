module ConflictingDefsDiffPatLambda where

foo : Int -> Int -> Int
foo = \(x : Int) (x : Int) -> 5