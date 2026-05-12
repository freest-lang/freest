module SendAndClose where

main : Int
main = forkWith #1 (sendAndClose 5) |> receiveAndWait
