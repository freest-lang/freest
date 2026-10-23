-- The sending side is forked; the main thread receives, so that the program
-- ends with every channel buffer empty.

g : !Int; Close -> Close
g c = send 5 c

_ = 
  let (x, y) = channel @(!Int;Close) in
  fork (\_ -1-> x |> g |> close);
  receiveAndWait @Int y
