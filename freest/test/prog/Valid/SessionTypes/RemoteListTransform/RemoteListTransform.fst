module RemoteListTransform where

type IntList : *T
type IntListC, IntListS : 1S
data IntList = Nil | Cons Int IntList
type IntListC = +{NilC: Skip, ConsC: !Int;IntListC;?Int}
type IntListS = &{NilC: Skip, ConsC: ?Int;IntListS;!Int}

transform : IntList -> IntListC;a -> (IntList, a)
transform list c =
    case list of
        Nil ->
            (Nil, select NilC c)
        Cons i rest ->
            let c = select ConsC c in
            let c = send i c in
            let (rest, c) = transform @(?Int ; a) rest c in
            let (y, c) = receive c in
            (Cons y rest, c)


listSum : IntListS;a -> (Int,a)
listSum c =
    case c of
        &NilC c ->
            (0, c)
        &ConsC c ->
            let (x, c) = receive c in
            let (rest, c) = listSum @(!Int ; a) c in
            let c = send (x + rest) c in
            (x+rest,c)

aCons, main : IntList

aCons = Cons 5 (Cons 4 (Cons 3 (Cons 2 (Cons 1 Nil))))

main =
    let (w, r) = channel @(IntListC;Close) in
    let _ = fork @() (\_:()1-> listSum @Wait r |> snd @Int @Wait |> wait) in
    let (l, c) = transform @Close aCons w in
    close c;
    l
