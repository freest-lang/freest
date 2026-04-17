module DualMessage where

sendInt : !Int;Close -> ()
sendInt c = c |> send 5 |> close

receiveInt : Dual (Dual (Dual !Int; Wait)) -> Int
receiveInt c = receiveAndWait c

main : Int
main =
  let (w,r) = channel @(Dual !Int;Wait) in
  fork (\(_ : ()) 1-> sendInt r);
  receiveInt w
