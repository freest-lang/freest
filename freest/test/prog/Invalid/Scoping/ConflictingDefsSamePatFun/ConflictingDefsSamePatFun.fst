module ConflictingDefsSamePatFun where

data Foo = Bar Int String

foo : Foo -> String
foo (Bar x x) = x