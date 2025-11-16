module SendListType where

type List : *T
data List = Cons Int List | Nil

type ListOut : 1S
type ListOut = +{NilC: Skip, ConsC: !Int;ListOut}

rcvList : forall (a : 1S). Dual ListOut;a -> (List, a)
rcvList @a c =
  case c of
    &ConsC c  ->
      let (i, c) = receive c in
      let (xs, c) = rcvList @a c in
      (Cons i xs, c)
    &NilC c  -> (Nil, c)

sendList : forall (a : 1S). ListOut;a -> List 1-> a
sendList @a c l =
  case l of
    Cons x xs ->
      let c = select ConsC c in
      let c = send x c in
      sendList @a c xs
    Nil       -> select NilC  c

aList, main : List

aList = Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))
main =
  let (x, y) = channel @(ListOut;Close) in
  let _      = fork @() (\(_ : ()) 1-> sendList @Close x aList |> close) in
  let (list, y) = rcvList @Wait y in
  wait y;
  list
