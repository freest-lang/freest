module SendInt where

main : Int
main =
  let (w, r) = channel @(!Int;Close) in
  let _ = fork @() (\(_:()) 1-> close (send @Int 5 @Close w)) in
-- Can't do this with synchronous channels because the writer blocks until it can synchronize with a reader.
--  let w1 = send w 5 in
  receiveAndWait @Int r 
