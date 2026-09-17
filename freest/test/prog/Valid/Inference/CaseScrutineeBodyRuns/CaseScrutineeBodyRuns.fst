-- Instantiating the scrutinee runs the type abstraction's body there.
f : forall a -> Maybe a
f @a = let _ = print @Int 7 in Nothing

main : ()
main =
  case f of
    Nothing -> print @Int 1
    Just _ -> print @Int 2
