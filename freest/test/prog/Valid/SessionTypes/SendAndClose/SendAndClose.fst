module SendAndClose where

main : Int
main = forkWith (sendAndClose 5) |> receiveAndWait
