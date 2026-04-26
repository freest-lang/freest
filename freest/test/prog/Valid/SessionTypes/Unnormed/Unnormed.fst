{- |
Module      :  Unnormed
Description :  An infinite interaction
Copyright   :  (c) Bernardo Almeida, Vasco T. Vasconcelos, Andreia Mordido

Note: In the web version, infinite programs that **print** values to
stdout, like this one, only show results after a system defined
timeout.

The writer is expected to write recursively and in the end read as
many times as were written on the channel.  In practice, interactions
on a channel described by T are interactions in which the writer
writes infinitely, because it is impossible to reach the state where
the writer supposedly reads the integers back from the channel.

FreeST builds on a novel algorithm for deciding type equivalence of
context-free session types. (see the algorithm at Almeida B., Mordido
A., Vasconcelos V.T. "Deciding the bisimilarity of context-free
session types").

The type !Int;T;?Int is equivalent to the type !Int;T because
unreachable sequences are pruned during the algorithm that decides
whether two context-free session types are equivalent.

-}

module Unnormed where

type T : 1C
type T = !Int; T; ?Int

writer : Int -> T -> ()
writer i c =
  let _ = writer (i + 1) (send i c)
  in ()

reader : Dual T -> ()
reader c =
  let (i, c) = receive c in
  print i;
  reader c

main : ()
main =
  let (w, r) = channel @T in
  fork (\(_ : ()) 1-> writer 0 w);
  reader r
