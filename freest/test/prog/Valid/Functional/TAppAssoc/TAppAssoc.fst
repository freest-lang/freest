module TAppAssoc where

g : !Int; Close -> Close
g c = send 5 c

main : ()
main = 
  let (x, y) = channel @(!Int;Close) in
  fork (\(_ : ()) -1-> receiveAndWait y);
  x |> g |> close
   
