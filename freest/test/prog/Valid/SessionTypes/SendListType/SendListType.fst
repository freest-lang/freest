module SendListType where

type List : *T
data List = Cons Int List | Nil

type ListOut : 1S
type ListOut = +{NilC: Skip, ConsC: !Int; ListOut}

rcvList : forall (a : 1S) -> Dual ListOut; a -> (List, a)
rcvList @a c =
  case c of
    &NilC  c  -> (Nil, c)
    &ConsC c  -> (Cons i xs, c)
      where (i , c) = receive c
            (xs, c) = rcvList c

sendList : forall (a : 1S) -> List -> ListOut; a -> a
sendList @a l c =
  case l of
    Nil       -> c |> select NilC
    Cons x xs -> c |> select ConsC |> send x |> sendList xs

main : ()
main =
  let (o, i) = channel @(ListOut; Close) 
      xs = Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))) in
  fork (\(_ : ()) -1-> o |> sendList xs |> close);
  let (ys, Wait) = rcvList i in
  print ys
