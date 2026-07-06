module SendClose where

writeFive : !Int ; Close -> ()
writeFive c =
  c ; ()

{-
writeFive' : !Int ; Close -> ()
writeFive' c =
  let c' = send 5 c
  in close c'

writeFive' : !Int ; Close -> ()
writeFive' c =
  close (send 5 c)

writeFive'' : !Int ; Close -> ()
writeFive'' c =
  c |> send 5 |> close

-- writeFive''' : !Int ; Close -> ()
-- writeFive''' = sendAndClose 5

receiveInt : ?Int ; Wait -> ()
receiveInt c =
  let (_, c') = receive c in wait c'

receiveInt' : ?Int ; Wait -> Int
receiveInt' c =
  let (x, c') = receive c in wait c' ; x

receiveInt'' : ?Int ; Wait -> Int
receiveInt'' = receiveAndWait
-}