module Fact10 where

type Choice : 1S
type Choice = +{More: !Int;Choice, Enough: Skip}

sendInt : forall (a : 1S). Int -> (Choice; a) -> a
sendInt @a 0 c = c |> select Enough
sendInt @a i c = c |> select More   |> send i |> sendInt @a (i - 1)

rcvInt : forall (a : 1S). Int -> (Dual Choice; a) -> (Int, a)
rcvInt @a acc c =
  case c of
    &Enough c -> (acc,c)
    &More c ->
      let (i, c) = receive c in
      let (iii, c) = rcvInt @a (acc*i) c in
      (iii, c)

main : Int
main =
  let (w, r) = channel @(Choice;Close) in
  fork (\(_ : ()) 1-> w |> sendInt @Close 10 |> close);
  let (i, r) = rcvInt @Wait 1 r in 
  wait r;
  i
