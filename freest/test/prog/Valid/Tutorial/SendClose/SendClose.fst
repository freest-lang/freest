module SendClose where

writeFive : !Int ; Close -> ()
writeFive c =
  c ; ()

writeFive : !Int ; Close -> ()
writeFive c =
  let c' = send 5 c in close c'

writeFive' : !Int ; Close -> ()
writeFive' c =
  close (send 5 c)

writeFive'' : !Int ; Close -> ()
writeFive'' c =
  c |> send 5 |> close

writeFive''' : !Int ; Close -> ()
writeFive''' = sendAndClose 5

readInt : ?Int ; Wait -> ()
readInt c =
  let (_, c') = receive c in wait c'

readInt' : ?Int ; Wait -> Int
readInt' c =
  let (x, c') = receive c in wait c' ; x

readInt'' : ?Int ; Wait -> Int
readInt'' = receiveAndWait

_ =
  let x = forkWith writeFive
  in print $ readInt' x