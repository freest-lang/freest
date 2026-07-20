data Tree a = Leaf | Node (Tree a) a (Tree a)

type TreeC a = +{Leaf: Skip, Node: TreeC a ; !a ; TreeC a}

marshall : forall a -> Tree a -> TreeC a; Close -> ()
marshall t c = c |> mars t |> close
    where
      mars : forall a b -> Tree a -> TreeC a ; b -> b
      mars Leaf         c = c |> select Leaf
      mars (Node l x r) c = c |> select Node |> mars l |> send x |> mars r

unmarshall : forall a -> Dual (TreeC a) ; Wait -> Tree a
unmarshall c =
    let (t, c) = unmars c
    in wait c ; t
    where
        unmars : forall a b -> Dual (TreeC a) ; b -> (Tree a, b)
        unmars @a @b (&Leaf c) = (Leaf, c)
        unmars @a @b (&Node c) =
            let (l, c) = unmars @a @(?a ; Dual (TreeC a); b) c
                (x, c) = receive c
                (r, c) = unmars @a @b c
            in (Node l x r, c)

aTree : Tree Int
aTree = Node (Node Leaf 1 Leaf) 2 (Node (Node Leaf 3 Leaf) 4 Leaf)

_ = forkWith (marshall aTree) |> unmarshall |> print
