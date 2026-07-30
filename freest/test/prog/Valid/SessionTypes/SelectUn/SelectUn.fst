-- `select_` returns its channel, like `send_`, so it pipelines and can be
-- partially applied.

type C : *C
type C = *+{L, M}

pickL : C -> C
pickL = select_ L

main : ()
main =
  let (w, r) = channel @C in
  w |> select_ L |> select_ M |> pickL;
  case r of *&L -> case r of *&M -> case r of *&L -> print 1
