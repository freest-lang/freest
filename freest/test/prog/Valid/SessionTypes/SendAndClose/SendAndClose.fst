main : ()
main = forkWith (sendAndClose 5) |> receiveAndWait |> print
