module ListRW where

data IList = Nil | Cons Int IList

type IListW = +{NilC: Skip, ConsC: !Int; IListW}

iListW : IList -> IListW;a -> a
iListW xs c =
  case xs of
    Nil -> select NilC c
    Cons x xs -> select ConsC c |> send x |> iListW  @a xs

iListR : (dualof IListW);a -> (IList, a)
iListR c =
  case c of
    NilC c -> (Nil, c)
    ConsC c -> let (x, c) = receive c in
               let (xs, c) = iListR @a c in
               (Cons x xs, c)

iFold : forall a:1T b:1S . a -> (Int -> a -> a) 1-> (dualof IListW);b 1-> (a, b)
iFold n f c =
  case c of
    NilC c -> (n, c)
    ConsC c -> let (m, c) = receive c in
               let (n, c) = iFold  @a @b n f c in
               (f m n, c)

iListR' : forall a: 1S . (dualof IListW);a -> (IList, a)
iListR' c = iFold @IList @a Nil Cons c

iLength : (dualof IListW);a -> (Int, a)
iLength c =
  case c of
    NilC c -> (0, c)
    ConsC c -> let (m, c) = receive c in
               let (n, c) = iLength  @a c in
               (m + n, c)

iLength' : (dualof IListW);a -> (Int, a)
iLength' x = iFold @Int @a 0 (+) x

aList : IList
aList = Cons 5 (Cons 3 (Cons 7 (Cons 1 Nil)))

main : Int
main = let (w, r) = new @(IListW;Close) () in
       fork @() (\_:() 1-> iListW @Close aList w |> close);
       let (i, r) = iLength' @Wait r in 
       wait r;
       i