module SendAsSendArg where

f1 : !Int; !Int; Close -> ()
f1 c = send 5 c |> send 5 |> close

f2 : ?Int; ?Int; Wait -> Int
f2 c = x1 + x2
  where (x1, c) = receive c
        x2      = receiveAndWait c

main : Int
main =
  let (c1, c2) = channel @(!Int; !Int; Close)
  in fork (\(_ : ()) 1-> f1 c1); f2 c2
