main : ()
main = forkWith (\c -> receiveAndClose c) |> sendAndWait 5
