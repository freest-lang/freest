module ListSend where

type SendList, RecvList : 1S
type SendList = +{Nil: Skip, Cons: !Int; SendList}
type RecvList = Dual SendList

flatten : forall (a : 1S) -> [Int] -> SendList; a -> a
flatten @a l c =
  case l of
    []     -> select Nil c
    h :: t -> c |> select Cons |> send h |> flatten t

reconstruct : forall (a : 1S) -> RecvList; a -> ([Int], a)
reconstruct @a c =
  case c of
    &Nil c -> ([] @Int, c)
    &Cons c ->
      let (h, c) = receive c
          (t, c) = reconstruct c
      in (h :: t, c)

main : [Int]
main =
  let (w, r) = channel @(SendList;Close) in
  fork #1 (\(_ : ()) -1-> flatten ([5, 7, 2, 6, 3] @Int) w |> close);
  let (l, c) = reconstruct r in 
  wait c;
  l
