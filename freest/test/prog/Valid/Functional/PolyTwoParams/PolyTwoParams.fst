module PolyTwoParams where

-- mkPair : forall (a : 1T) . forall (b : 1T) . a -> b 1-> (a, b)
mkPair : forall (a b : 1T). a -> b 1-> (a, b)
mkPair @a @b x y = (x, y)

main : (Int, Bool)
main =
  let (r, w) = channel @(Skip;Wait) in
  let (i, s) = mkPair @Int @(Skip;Wait) 4 r in
  (;) @() @(Int, Bool)
    (fork @() (\(_:()) 1-> close w))
    ((;) @() @(Int, Bool)
      (fork @() (\(_:()) 1-> wait s))
      (mkPair @Int @Bool i True))
