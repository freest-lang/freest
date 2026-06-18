module SendAndWait where

main : ()
main = forkWith receiveAndClose |> sendAndWait 5
