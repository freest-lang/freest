-- The control for LinChanTypeConfusion.
mk : forall a -> () -> (!a;Close, ?a;Wait)
mk @a _ = channel @(!a;Close)

main : ()
main =
  let (c, s) = mk @Int () in
  fork @() (\_ -1-> c |> send 5 |> close);
  let (x, s) = receive s in
  wait s;
  print @Char x
