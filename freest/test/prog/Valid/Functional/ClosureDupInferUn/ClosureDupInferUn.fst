{- Usage inference through a closure. `x` is captured by `g` and `g` is an
   unrestricted closure invoked twice, so `x` is effectively used twice and
   its type parameter `a` must be inferred unrestricted (*T) — without an
   annotation. Before usage scaled by the closure's multiplicity, `a` was
   inferred linear and this was rejected. -}
module ClosureDupInferUn where

dupC : forall a -> a -> (a, a)
dupC @a x = let g = \(u:()) -> x in (g (), g ())

main : ()
main = let (a, b) = dupC @Int 3 in print (a + b)
