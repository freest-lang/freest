-- `map`'s result is bound to `send`'s type before `o` fixes its continuation;
-- the continuation must still reach the expected type of `map`'s argument.
main : ()
main =
  let (o, i) = channel @(!Int ; Wait) in
  fork (\_ -1-> (head (map send [5])) o |> wait);
  print (receiveAndClose i)
