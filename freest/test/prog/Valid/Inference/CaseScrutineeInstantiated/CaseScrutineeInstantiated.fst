-- x is bound by name; matching it instantiates it, and n + 1 fixes the element type.
main : ()
main =
  let x = Nothing in
  case x of
    Nothing -> print @Int 1
    Just n -> print @Int (n + 1)
