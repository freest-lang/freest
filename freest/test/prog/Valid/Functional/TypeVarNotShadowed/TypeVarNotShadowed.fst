module TypeVarNotShadowed where

-- Type variables should not be shadowed by program variables.

-- implicit type abstraction
f : c -> Int
f c = f @c c

-- explicit type abstraction
trueC : forall (a : *T) -> a -> a -> a
trueC = \@a (a : a) (b : a) -> a

main : Int 
main = trueC @Int 0 1
