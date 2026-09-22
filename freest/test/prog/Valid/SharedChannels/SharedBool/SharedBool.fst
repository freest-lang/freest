type Bool' : *C
type Bool' = *+{False', True'}

true' : Bool' -> Void @*T
true' c = true' $ select_ True' c

false' : Bool' -> Void @*T
false' c = false' $ select_ False' c

cond : forall a -> Dual Bool' -> a -> a -> a
cond @a c v1 v2 = 
  case c of 
    *&True'  -> v1
    *&False' -> v2

main : ()
main =
  let (tw, tr) = channel @Bool' in
  let (fw, fr) = channel @Bool' in
  fork (\_ -1-> true' tw);
  fork (\_ -1-> false' fw);
  cond tr 1 2 + cond fr 3 4 |> print
