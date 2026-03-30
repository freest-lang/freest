{- |
Module      :  anbn
Description :  The context-free language {A^nB^n | n >= 1}
Copyright   :  (c) Bernardo Almeida, Andreia Mordido, Vasco T. Vasconcelos

The language of S0 is {A^nB^n | n >= 1}

S0 -> a S1
S1 -> a S1 b | b

The language generated from S0 is not regular.

This example is from unpublished notes by Frank Pfenning and Henry DeYoung
on a simplified representation of deterministic pushdown automata.
-}
module AnBn where

type S0, S1 : 1S
-- Production S0
type S0 = +{A: S1}
-- Production S1
type S1 = +{A: S1; +{B: Skip}, B: Skip}

-- for each A selected a B is also selected
client' : forall (a : 1S). Int -> S1;a -> a
client' @a 0 c = c |> select B
client' @a n c = c |> select A |> client' (n - 1) |> select B

-- The client selects a given number of A's
client : Int -> S0;Close -> ()
client n c = c |> select A |> client' (n - 1) |> close

-- For each A selected, a choice for B is also offered
server' : forall (a : 1S). Dual S1; a -> a
server' @a c =
  case c of
    &A c -> case server' c of
      &B c -> c
    &B c -> c

-- The server offers the choice composed by A
server : Dual S0; Wait -> ()
server c = case c of &A c -> c |> server' |> wait

main : ()
main =
  let (w, r) = channel @(S0;Close) in
  fork (\(_ : ()) 1-> w |> client 25);
  server r
