module CrossTypes where

type List : *T
data List = Cons Int List | Nil

type ListOut : 1S
type ListOut = +{Nil : Skip, Cons: !Int;ListOut}

rcvList : forall (a : 1S) -> (Dual ListOut; a) -> (List, a)
rcvList @a c =
  case c of
    &Cons c ->
      let (i, c) = receive c in
      let (xs, c) = rcvList c in
      (Cons i xs, c)
    &Nil c -> (Nil, c)

sendList : forall (a : 1S) -> (ListOut; a) -> List -1-> a
sendList @a c l =
  case l of
    Cons x xs ->
      let c = select Cons c in
      let c = send x c in
      sendList c xs
    Nil -> select Nil c

aList : List
aList = Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))

main : List
main =
  let (x, y) = channel @(ListOut; Close) in
  fork #1 (\(_ : ()) -1-> sendList y aList |> close); -- STRANGE ERROR
  let (list, x) = rcvList x in
  wait x;
  list

