main : ()
main = forkWith receiveAndClose |> sendAndWait 5
