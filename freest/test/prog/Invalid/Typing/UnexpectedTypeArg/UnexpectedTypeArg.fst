module UnexpectedTypeArg where

foo : Int
foo = (\(x : Int) -> x) @Int 0
