-- A tuple pattern matches pairOf, so the binding instantiates it.
pairOf : forall a -> (Maybe a, Int)
pairOf @a = (Nothing, 3)

main : ()
main =
  let (m, n) = pairOf in
  case m of
    Nothing -> print @Int n
    Just k -> print @Int (k + n)
