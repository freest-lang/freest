module InfiniteChannels where

-- Creates an unbounded number of channels; diverges
write : !Int;Close -> Int 1-> ()
write c n =
  let c = send @Int n @Close c in
  let _ = print @Int n in
  let (r, w) = channel @(!Int;Close) in
  let _ = fork @Int (\(_:()) 1-> receiveAndWait @Int w) in
  let _ = write r (n + 1) in
  close c

main : ()
main =
  let (r, w) = channel @(!Int;Close) in
  let _ = fork @Int (\(_:()) 1-> receiveAndWait @Int w) in
  write r 0
