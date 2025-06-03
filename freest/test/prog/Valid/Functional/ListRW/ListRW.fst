module ListRW where

type IList : *T
data IList = Nil | Cons Int IList

type IListW : 1S
type IListW = +{NilC: Skip, ConsC: !Int; IListW}

iListW : forall (a : 1S). IList -> IListW;a -> a
iListW @a xs c =
  case xs of
    Nil -> c |> select NilC
    Cons x xs -> c |> select ConsC |> send x |> iListW @a xs

iListR : forall (a : 1S). (Dual IListW);a -> (IList, a)
iListR @a c =
  case c of
    &NilC c  -> (Nil, c)
    &ConsC c -> let (x, c) = receive c in
                let (xs, c) = iListR @a c in
                (Cons x xs, c)

iFold : forall (a : 1T) (b : 1S). a -> (Int -> a -> a) 1-> (Dual IListW);b 1-> (a, b)
iFold @a @b n f c =
  case c of
    &NilC c  -> (n, c)
    &ConsC c -> let (m, c) = receive c in
                let (n, c) = iFold  @a @b n f c in
                (f m n, c)

iListR' : forall (a : 1S). (Dual IListW);a -> (IList, a)
iListR' @a c = iFold @IList @a Nil Cons c

iLength : forall (a : 1S). (Dual IListW);a -> (Int, a)
iLength @a c =
  case c of
    &NilC c  -> (0, c)
    &ConsC c -> let (m, c) = receive c in
                let (n, c) = iLength  @a c in
                (m + n, c)

iLength' : forall (a : 1S). (Dual IListW);a -> (Int, a)
iLength' @a x = iFold @Int @a 0 (+) x

aList : IList
aList = Cons 5 (Cons 3 (Cons 7 (Cons 1 Nil)))

main : Int
main = 
  let (w, r) = channel @(IListW;Close) in
  fork (\(_ : ()) 1-> iListW @Close aList w |> close);
  let (i, r) = iLength' @Wait r in 
  wait r;
  i