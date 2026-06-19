module SendAndClose where

main : ()
main = forkWith (sendAndClose 5) |> receiveAndWait |> print
