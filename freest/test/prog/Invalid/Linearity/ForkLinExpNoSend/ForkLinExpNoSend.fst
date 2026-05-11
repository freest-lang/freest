module ForkLinExpNoSend where

main : Int
main = 
  let (r, w) = channel @(?Int; Wait) in 
  fork #1 (\(_ : ()) -1-> w);
  receiveAndWait r
