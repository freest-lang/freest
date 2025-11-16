module PolyVarMonoContext where

f : forall (a : *T). a -> a
f @a x = x

main : Int
main =  f (f 5)
