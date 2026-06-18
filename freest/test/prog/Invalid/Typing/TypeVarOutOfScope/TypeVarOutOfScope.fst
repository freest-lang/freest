module TypeVarOutOfScope where

foo : forall (a : *T) -> a -> a
foo = (\@(a : *T) (x : b) -> x)