{- Capture-aware tightening: a `forall`-bound value captured across an
   unrestricted arrow (`-*->`) is used unrestrictedly, so the omitted binder is
   inferred `*T` (not the general `1T`) with no annotation. `konst @a x` is an
   unrestricted closure over `x : a`, so `a` must be `*T`. -}
module ForallCapture where

konst : forall a -> a -*-> forall (b:1S) -> () -1-> a
konst @a x @b () = x
