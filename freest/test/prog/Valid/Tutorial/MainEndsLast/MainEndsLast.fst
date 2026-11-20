writeFive : !Int ; Close -> ()
writeFive = sendAndClose 5

readInt : ?Int ; Wait -> ()
readInt c =
  let (x, c') = receive c in print x ; wait c'

-- Expect "5"
_ = forkWith writeFive |> readInt

-- An incorrect program: expect "5" or no output
-- _ = forkWith readInt |> writeFive

