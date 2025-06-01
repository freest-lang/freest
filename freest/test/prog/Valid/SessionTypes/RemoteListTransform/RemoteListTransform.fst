module RemoteListTransform where

type IntList : *T
type IntListC, IntListS : 1S
data IntList = Nil | Cons Int IntList
type IntListC = +{NilC: Skip, ConsC: !Int;IntListC;?Int}
type IntListS = &{NilC: Skip, ConsC: ?Int;IntListS;!Int}

transform : forall (a : 1S). IntList -> IntListC;a -> (IntList, a)
transform @a list c =
  case list of
    Nil -> (Nil, select NilC c)
    Cons i rest ->
      let c = select ConsC c in
      let c = send @Int i @(IntListC;?Int;a) c in
      let (rest, c) = transform @(?Int ; a) rest c in
      let (y, c) = receive @Int @a c in
      (Cons y rest, c)

listSum : forall (a : 1S). IntListS;a -> (Int,a)
listSum @a c =
  case c of
    &NilC c -> (0, c)
    &ConsC c ->
      let (x, c) = receive @Int @(IntListS;!Int;a) c in
      let (rest, c) = listSum @(!Int ; a) c in
      let c = send @Int (x + rest) @a c in
      (x+rest,c)

aCons, main : IntList

aCons = Cons 5 (Cons 4 (Cons 3 (Cons 2 (Cons 1 Nil))))

main =
    let (w, r) = channel @(IntListC;Close) in
    let _ = fork @() (\(_:()) 1-> wait (snd @Int @Wait (listSum @Wait r))) in
    let (l, c) = transform @Close aCons w in
    let _ = close c in
    l
