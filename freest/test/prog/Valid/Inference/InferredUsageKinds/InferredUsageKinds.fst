module InferredUsageKinds where

-- Usage-based multiplicity inference: with no kind written on `forall a`, a
-- parameter that is duplicated or discarded forces `a` to `*T`, while a
-- linearly-used one stays the most general `1T`.

dup : forall a -> a -> (a, a)        -- x duplicated => a : *T
dup @a x = (x, x)

discard : forall a -> a -> Int       -- x discarded  => a : *T
discard @a x = 42

pick : forall a -> Bool -> a -> a -> a  -- one arg dropped per branch => a : *T
pick @a b x y = if b then x else y

dropPair : forall a -> (a, a) -> Int    -- composite param discarded => a : *T
dropPair @a p = 99

dupComp : forall a -> (a, a) -> (a, a, a)  -- a destructured component duplicated => a : *T
dupComp @a p = let (x, y) = p in (x, y, x)

-- a constructor-pattern binder discarded: `x` (the field, of type `a`) is
-- dropped, so `a : *T` is inferred — without it, `a` defaults to `1T` and the
-- linear `x` would be rejected, so this only compiles thanks to the inference.
data Box (a : 1T) = MkBox a
useBox : forall a -> Box a -> Int
useBox @a b = case b of MkBox x -> 77

main : ()
main =
  let (p, q) = dup @Int 7 in
  let (r, s, t) = dupComp @Int (5, 6) in
  print (p + q + discard @Char 'z' + pick @Int True 1 2 + dropPair @Int (3, 4)
         + r + s + t + useBox @Int (MkBox 8))
