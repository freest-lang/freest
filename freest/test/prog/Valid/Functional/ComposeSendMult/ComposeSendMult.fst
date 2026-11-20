sendThenClose : forall #m (a : m T) -> a -> !a ; Close -m-> ()
sendThenClose #m @a = (close .) . send

main : ()
main =
  let (o, i) = channel @(!Int ; Close) in
  sendThenClose 5 o;
  print (receiveAndWait i)
