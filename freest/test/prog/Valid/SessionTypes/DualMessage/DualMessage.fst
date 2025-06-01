module DualMessage where

sendInt : !Int;Close -> ()
sendInt c = close (send @Int 5 @Close c)

receiveInt : Dual (Dual (Dual !Int;Wait)) -> Int
receiveInt c = receiveAndWait @Int c

main : Int
main =
  let (w,r) = channel @(Dual !Int;Wait) in
  let _ = fork @() (\(_:()) 1-> sendInt r) in 
  receiveInt w
