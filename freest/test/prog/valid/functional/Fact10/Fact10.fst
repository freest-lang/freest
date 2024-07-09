module Fact10 where
{-abbbbcbcb-}
type Choice = +{More: !Int;Choice, Enough: Skip}

sendInt : Int -> Choice;a -> a
sendInt i c =
  if i == 0 then
    select {- abc -} Enough c -- abc
  else
    let c = select More c in
    let c = send i c in
    sendInt @a (i - 1) c

rcvInt : Int -> (dualof Choice);a -> (Int, a)
rcvInt acc c =
  case c of
    Enough c -> (acc,c)
    More c ->
      let (i, c) = receive c in
      let (iii, c) = rcvInt @a (acc*i) c in
      (iii, c)

main : Int
main =
  let (w, r) = channel @(Choice;Close)
      _ = fork @() (\_:() 1-> sendInt @Close 10 w |> close)
      (i, r) = rcvInt @Wait 1 r 
  in wait r; i
