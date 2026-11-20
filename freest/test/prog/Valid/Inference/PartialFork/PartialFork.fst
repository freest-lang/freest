myfork : forall #m a -> (() -m-> a) -> ()
myfork = fork

_ =
  let (r, w) = channel @(?Int;Wait) in
  myfork (\_ -1-> send 5 w |> close) ;
  print (receiveAndWait r)
