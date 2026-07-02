module PartialFork where

myfork : forall #m a -> (() -m-> a) -> ()
myfork = fork

main : ()
main =
  let (r, w) = channel @(?Int;Wait) in
  myfork (\_ -1-> send 5 w |> close) ;
  print (receiveAndWait r)
