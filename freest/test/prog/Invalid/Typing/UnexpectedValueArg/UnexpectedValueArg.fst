module UnexpectedValueArg where

foo : Int
foo = (\@(a : *T) (x : a) -> x) 0
