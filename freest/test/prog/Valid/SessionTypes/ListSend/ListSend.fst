module ListSend where

type List : *T
data List = Nil | Cons Int List

type SendList, RecvList : 1S
type SendList = +{Nil: Skip, Cons: !Int;SendList}
type RecvList = Dual SendList

flatten : List -> SendList;a -> a
flatten l c =
  case l of
    Nil -> select Nil c
    Cons h t ->
      let c = select Cons c in
      let c = send h c in
      flatten @a t c

reconstruct : RecvList;a -> (List, a)
reconstruct c =
  case c of
    &Nil c -> (Nil, c)
    &Cons c ->
      let (h, c) = receive c in
      let (t, c) = reconstruct @a c in
      (Cons h t, c)

aList, main : List

aList = Cons 5 (Cons 7 (Cons 2 (Cons 6 (Cons 3 Nil))))

main =
  let (w, r) = channel @(SendList;Close) in
  fork @() (\_:()1-> flatten @Close aList w |> close);
  let (l, c) = reconstruct @Wait r in 
  wait c;
  l
