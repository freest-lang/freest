module ProperKindMismatchParam where

type Foo : *T -> *T
type Foo a = a

foo = (\(x : Foo) -> 1)