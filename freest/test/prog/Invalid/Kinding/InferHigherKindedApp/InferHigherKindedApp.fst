module InferHigherKindedApp where

f : forall (h : *T -> *T) -> Int
f @h = 0

k : Int
k = f
