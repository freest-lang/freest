-- This is clearly a buggy program.
-- It may end with '5' and 'close' in the buffer.
-- To get it right fork the sending side instead.

g : !Int; Close -> Close
g c = send 5 c

_ = 
  let (x, y) = channel @(!Int;Close) in
  fork (\_ -1-> receiveAndWait y);
  x |> g |> close
