compose : 
  forall #m #n (a : 1T) (b : 1T) (c : 1T) 
  -*->   (b -m-> c) 
  -*->   (a -n-> b) 
  -m->   a 
  -m+n-> c
compose #m #n @a @b @c f g x = f (g x)

sendAndClose : forall #m (a : m T) -> a -> !a ; Close -m-> () -- TODO: move to Prelude
sendAndClose #m @a = (close .) . send -- errors when making parameters implicit, applying @Close to send, etc...

main : ()
main =
  let plusTwo = succ . succ
      (o, i) = channel @(!Int; Close) 
      sendPlusTwo = close . (flip send o) . plusTwo
  in sendPlusTwo 0;
     print (receiveAndWait i)
