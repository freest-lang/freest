-- `send` composed point-free: its session continuation `b` is instantiated to
-- `Close` by `close .`, which needs `send`'s quantifiers in prenex position.
sendThenClose : forall (a : *T) -> a -> !a ; Close -> ()
sendThenClose @a = (close .) . send

main : ()
main =
  let (o, i) = channel @(!Int ; Close) in
  sendThenClose 5 o;
  print (receiveAndWait i)
