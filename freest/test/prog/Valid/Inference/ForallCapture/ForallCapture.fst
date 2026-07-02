{- A `forall`-bound value captured across an unrestricted arrow (`-*->`): the
   partial application `konst @a x` is unrestricted, so it may be entered many
   times and `x : a` must be `*T`. The omitted binder defaults to the general
   `1T`; plain duplication is already tightened to `*T`, but this capture is not.
   Passes today only with the annotation `forall (a : *T)`. -}
module ForallCapture where

konst : forall a -> a -*-> forall (b:1S) -> () -1-> a
konst @a x @b () = x
