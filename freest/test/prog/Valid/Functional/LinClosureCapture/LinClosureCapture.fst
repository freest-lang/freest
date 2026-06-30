{- The dual of ClosureDupInferUn: `g` is a LINEAR closure (-1->) invoked once,
   so `x` is used once and `a` must stay linear-capable — it must NOT be forced
   to *T. Instantiated at a linear type (Int -1-> Int), which a *T would reject.
   Guards the multiplicity-aware usage scaling against over-forcing. -}
module LinClosureCapture where

once : forall a -> a -> a
once @a x = let g = \(u:()) -1-> x in g ()

main : ()
main = let f = once @(Int -1-> Int) (\(z:Int) -1-> z) in print (f 3)
