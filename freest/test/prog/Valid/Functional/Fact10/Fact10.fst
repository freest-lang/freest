module Fact10 where

type Choice = +{More: !Int;Choice, Enough: Skip}

sendInt : forall (a : 1S) -> Int -> (Choice; a) -> a
sendInt @a 0 c = c |> select Enough
sendInt @a i c = c |> select More   |> send i |> sendInt (i - 1)

rcvInt : forall (a : 1S) -> Int -> (Dual Choice; a) -> (Int, a)
rcvInt @a acc c =
  case c of
    &Enough c -> (acc,c)
    &More c ->
      let (i, c) = receive c in
      let (iii, c) = rcvInt (acc*i) c in
      (iii, c)

rt : forall (a : *T) (b : *T) -> a -> (a -> b) -> b
rt @a @b x f = f x

main : Int
main =
  let (w, r) = channel @(Choice;Close) in
  fork (\(_ : ()) -1-> w |> sendInt 10 |> close);
  let (i, r) = rcvInt 1 r in 
  wait r;
  i
