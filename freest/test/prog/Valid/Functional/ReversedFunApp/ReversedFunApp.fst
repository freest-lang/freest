module ReversedFunApp where

f : forall (a b : *T). a -> (a -> b) -> b -- ∀a:*T. ∀b:*T. a -> (a -> b) -> b
f = (|>)

main : Int
main = f @Int @Int 5 (\(x : Int) -> x)

