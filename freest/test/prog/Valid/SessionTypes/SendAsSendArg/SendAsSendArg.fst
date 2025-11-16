module SendAsSendArg where

f1 : !Int;!Int;Close -> ()
f1 c = send 5 c |> send 5 |> close

f2 : ?Int;?Int;Wait -> Int
f2 c =
  let (x1, c) = receive c in
  let x2      = receiveAndWait @Int c in 
  x1 + x2

main : Int
main =
  let (c1, c2) = channel @(!Int;!Int;Close) in
  let _ = fork @() (\(_ : ()) 1-> f1 c1) in
  f2 c2 -- in x
