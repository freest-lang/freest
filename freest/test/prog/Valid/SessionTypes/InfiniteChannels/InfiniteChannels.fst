module InfiniteChannels where

-- Creates an unbounded number of channels; diverges
write : !Int;Close -> Int 1-> ()
write c n =
  let c = send n c in
  print @Int n ;
  let (r, w) = channel @(!Int;Close) in
  fork (\_:()1-> receiveAndWait @Int w); 
  write r (n + 1) ;
  close c

main : ()
main =
  let (r, w) = channel @(!Int;Close) in
  fork (\_:()1-> receiveAndWait @Int w);
  write r 0
