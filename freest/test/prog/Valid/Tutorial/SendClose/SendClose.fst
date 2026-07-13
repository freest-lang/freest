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




_ = forkWith writeFive |> readInt' |> print

-- _ = print $ readInt' $ forkWith writeFive

-- The same, using pattern matching
readInt : ?Int ; Wait -> ()
readInt (?x ; Wait) = print x









-- A more complex protocol
sumThree : ?Int ; ?Int ; ?Int ; Wait -> ()
sumThree (?x ; ?y ; ?z ; Wait) = print $ x + y + z
