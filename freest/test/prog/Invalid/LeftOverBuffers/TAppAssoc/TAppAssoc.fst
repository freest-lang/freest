-- Ends with '5' and 'close' in a buffer: the main thread sends and closes,
-- and terminates before the forked thread receives. The fixed version, in
-- Valid/Functional/TAppAssoc, forks the sending side instead.

g : !Int; Close -> Close
g c = send 5 c

_ = 
  let (x, y) = channel @(!Int;Close) in
  fork (\_ -1-> receiveAndWait y);
  x |> g |> close
