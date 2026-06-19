{-

This program deadlocks with communication buffers of size 1, which is
what you get with an implementation with two MVars per channel. It
does not deadlock with buffers of size 2.

-}

module Deadlock where

writer : !Char;!Char;Close -> !Bool;!Bool;Close -1-> ()
writer w1 w2 =
  let w1 = send 'c' w1 |> send 'd' in
  let w2 = send True w2 |> send False in 
  close w1; close w2 

reader : ?Char;?Char;Wait -> ?Bool;?Bool;Wait -1-> Bool
reader r1 r2 =
  let (x, r2) = receive r2 in
  let (x, r2) = receive r2 in
  let (y, r1) = receive r1 in
  let (y, r1) = receive r1 in
  wait r1; wait r2;
  x

main : ()
main =
  let (w1, r1) = channel @(!Char;!Char;Close) in
  let (w2, r2) = channel @(!Bool;!Bool;Close) in
  fork (\(_ : ()) -1-> writer w1 w2);
  print (reader r1 r2)
