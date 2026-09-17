-- Each case instantiates x anew, so the two matches may use different element types.
main : ()
main =
  let x = Nothing in
  case x of
    Nothing -> print @Int 1
    Just n -> print @Int n
  ;
  case x of
    Nothing -> print @Int 2
    Just c -> print @Char c
