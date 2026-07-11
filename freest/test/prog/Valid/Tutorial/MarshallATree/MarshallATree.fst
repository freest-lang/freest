data Tree a = Leaf | Node (Tree a) a (Tree a)

type TreeC a = +{Leaf: Skip, Node: TreeC a ; !a ; TreeC a}

marshall : forall a -> Tree a -> TreeC a; Close -> ()
marshall tree c = marsh tree c |> close
    where
      marsh : forall a b -> Tree a -> TreeC a; b -> b
      marsh Leaf         c = c |> select Leaf
      marsh (Node l x r) c = c |> select Node |> marsh l |> send x |> marsh r

unmarshall : forall a -> Dual (TreeC a) ; Wait -> Tree a
unmarshall c =
    let (tree, c) = unmarsh c
    in wait c ; tree
    where
        unmarsh : forall a b -> Dual (TreeC a) ; b -> (Tree a, b)
        unmarsh @a @b (&Leaf c) = (Leaf, c)
        unmarsh @a @b (&Node c) =
            let (l, c) = unmarsh @a c
                (x, c) = receive c
                (r, c) = unmarsh @a c
            in (Node l x r, c)

aTree : Tree Int
aTree = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)

_ = forkWith (marshall aTree) |> unmarshall |> print

