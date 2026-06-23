module PolyTwoParams where

-- mkPair : forall (a : 1T) -> forall (b : 1T) -> a -> b -1-> (a, b)
mkPair : forall (a : 1T) (b : 1T) -> a -> b -1-> (a, b)
mkPair @a @b x y = (x, y)

main : ()
main =
  let (r, w) = channel @(Skip;Wait) in
  let (i, s) = mkPair 4 r in
  fork (\(_ : ()) -1-> close w);
  fork (\(_ : ()) -1-> wait s);
  print (mkPair i True)
