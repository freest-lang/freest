module TAppAssoc where

g : !Int;Close -> Close
g c =  (send  @Int 5)  @Close c

main : ()
main = 
  let (x, y) = channel @(!Int;Close) in
  let _ = fork @Int (\_:() 1-> (receiveAndWait @Int y)) in
  g x |> close
   
