module SharedBool where

type Bool' : *C
type Bool' = *+{False', True'}

true' : Bool' -> Diverge
true' c = true' $ select True' c

false' : Bool' -> Diverge
false' c = false' $ select False' c

cond : forall (a : *T) . Dual Bool' -> a -> a -> a
cond @a c v1 v2 = 
  case c of 
    &True'  _ -> v1
    &False' _ -> v2

main : Int
main =
  let (tw, tr) = channel @Bool' in
  let (fw, fr) = channel @Bool' in
  fork (\(_ : ()) 1-> true' tw);
  fork (\(_ : ()) 1-> false' fw);
  cond @Int tr 1 2 + cond @Int fr 3 4
  -- 1
