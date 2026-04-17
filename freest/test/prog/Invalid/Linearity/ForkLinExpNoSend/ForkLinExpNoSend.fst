module ForkLinExpNoSend where

main : Int
main = 
  let (r, w) = channel @(?Int; Wait) in 
  fork (\(_ : ()) 1-> w);
  receiveAndWait r
