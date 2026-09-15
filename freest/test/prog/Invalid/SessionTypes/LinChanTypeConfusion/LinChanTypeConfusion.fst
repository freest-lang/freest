-- Linear ends used once each: linearity does not stop the escaped type variable
-- from being re-bound, so an Int is sent and a Char received.
mk : forall a -> () -> (!a;Close, ?a;Wait)
mk @a _ = channel @(!a;Close)

main : ()
main =
  let (c, s) = mk () in
  fork @() (\_ -1-> c |> send 5 |> close);
  let (x, s) = receive s in
  wait s;
  print @Char x
