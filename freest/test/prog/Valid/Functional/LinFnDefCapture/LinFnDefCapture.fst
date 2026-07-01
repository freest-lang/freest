{- The local-function analog of LinClosureCapture. `f` is a LINEAR local
   function (-1->) that captures `x` and is invoked once, so `x` is used once
   and `a` must stay linear-capable. Before usage was scaled by the local
   function's signature multiplicity, a single-clause capture was reported as
   `Many` (mergeU has no identity), forcing `a` to *T and rejecting the linear
   instantiation. -}
module LinFnDefCapture where

once : forall a -> a -> a
once @a x =
  let f : () -1-> a
      f u = x
  in f ()

main : ()
main = let g = once @(Int -1-> Int) (\(z:Int) -1-> z) in print (g 3)
