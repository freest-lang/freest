module CrossTypes1 where

type ListOut, ListIn : 1S
type ListOut = +{Nil : Skip, Cons: !Int;ListOut}
type ListIn = Dual ListOut

rcvList : forall (a : 1S) -> (ListOut; a) -> ([Int], a)
rcvList @a c =
  case c of
    &Cons c ->
      let (i, c) = receive c in
      let (xs, c) = rcvList c in
      (i :: xs, c)
    &Nil c -> ([] @Int, c)

sendList : forall (a : 1S) -> [Int] -> (ListIn; a) -> a
sendList @a []        c = select Nil c
sendList @a (x :: xs) c = c |> select Cons |> send x |> sendList xs


main : [Int]
main =
  let (x, y) = channel @(ListOut; Close) in
  fork #1 (\(_ : ()) -1-> sendList x aList |> close);
  let (list, y) = rcvList y in
  wait y; 
  list

aList : [Int]
aList = [2,3,4,5] @Int
