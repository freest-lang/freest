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

main : ()
main =
  let (p, q) = dup @Int 7 in
  print (p + q + discard @Char 'z' + pick @Int True 1 2 + dropPair @Int (3, 4))
