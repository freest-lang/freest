module RemoteListTransform where

type IntList : *T
type IntListC, IntListS : 1S
data IntList = Nil | Cons Int IntList
type IntListC = +{NilC: Skip, ConsC: !Int;IntListC;?Int}
type IntListS = &{NilC: Skip, ConsC: ?Int;IntListS;!Int}

transform : forall (a : 1S) -> IntList -> (IntListC; a) -> (IntList, a)
transform @a list c =
    case list of
        Nil ->
            (Nil, select NilC c)
        Cons i rest ->
            let (rest, c) = c |> select ConsC 
                              |> send i 
                              |> transform rest in
            let (y, c) = receive c in
            (Cons y rest, c)


listSum : forall (a : 1S) -> (IntListS; a) -> (Int, a)
listSum @a c =
    case c of
        &NilC c ->
            (0, c)
        &ConsC c ->
            let (x, c) = receive c in
            let (rest, c) = listSum c in
            let c = send (x + rest) c in
            (x+rest,c)

aCons, main : IntList

aCons = Cons 5 (Cons 4 (Cons 3 (Cons 2 (Cons 1 Nil))))

main =
    let (w, r) = channel @(IntListC;Close) in
    fork #1 (\(_ : ()) -1-> r |> listSum |> snd |> wait);
    let (l, c) = transform aCons w in
    close c;
    l
