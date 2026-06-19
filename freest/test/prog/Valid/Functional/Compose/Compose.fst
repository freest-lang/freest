module Compose where

compose : 
  forall #m #n (a : 1T) (b : 1T) (c : 1T) 
  -*->   (b -m-> c) 
  -*->   (a -n-> b) 
  -m->   a 
  -m+n-> c
compose #m #n @a @b @c f g x = f (g x)

send' : forall #m (a : m T) -> a -> forall (b : 1S) -> !a;b -m-> b -- TODO: move to Prelude
send' = undefined @(forall #m (a : m T) -> a -> forall (b : 1S) -> !a;b -m-> b)

sendAndClose : forall #m (a : m T) -> a -> !a ; Close -m-> () -- TODO: move to Prelude
sendAndClose #m @a = compose (compose close) (\(x : a) -> send' x @Close)

main : Int
main =
  let plusTwo = compose succ succ
      -- succAfter = (.) succ
      (o, i) = channel @(!Int; Close) 
      sendPlusTwo = compose (\(x : Int) -1-> close (send x o)) plusTwo 
      sendAfter = (.) (\(x : Int) -1-> close (send x o)) -- plusTwo
  in sendPlusTwo 0; print (receiveAndWait i)
     -- (succAfter (succAfter (id @Int))) 0; ()
-- <bucket: other>
