module PartialFork where

myfork : forall #m (a : *T) -> (() -m-> a) -> ()
myfork = fork

main : Int
main =
  let (r, w) = channel @(?Int;Wait) in
  myfork (\(_ : ()) -1-> send 5 w |> close) ;
  receiveAndWait r
  
