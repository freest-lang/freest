module SendAndWait where

main : ()
main = forkWith #* (receiveAndClose @Int) |> sendAndWait 5 -- CANNOT INFER
