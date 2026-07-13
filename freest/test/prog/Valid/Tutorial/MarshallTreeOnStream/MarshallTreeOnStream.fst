type Stream a = +{Done: Close, More: !a ; Stream a}

data Tree a = Leaf | Node (Tree a) a (Tree a)

marshall : forall a -> Tree a -> Stream (Maybe a) -> ()
marshall t c = marsh t c |> select Done |> close
    where
        marsh : forall a -> Tree a -> Stream (Maybe a) -> Stream (Maybe a)
        marsh @a Leaf         c =
            c |> select More |> send (Nothing @a)
        marsh @a (Node l x r) c =
            c |> select More |> send (Just x) |> marsh @a l |> marsh @a r

discard : forall a -> ?a ; Dual (Stream a) -> ()
discard c = let (_, c) = receive c in disc c
    where
        disc : forall a -> Dual (Stream a) -> ()
        disc @a (&Done c)        = wait c
        disc @a (&More (?_ ; c)) = disc @a c

unmarshall : forall a -> Dual (Stream (Maybe a)) -> Tree a
unmarshall c = case unmarsh c of
    (t, &Done c) -> wait c ; t
    (t, &More c) ->
        discard c ;
        error "Leftover tokens: the tree is complete yet the stream still offers More"
  where
        unmarsh : forall a -> Dual (Stream (Maybe a)) -> (Tree a, Dual (Stream (Maybe a)))
        unmarsh @a (&Done c) =
            wait c ;
            error "Truncated tree: a token is required but the stream has ended"
        unmarsh @a (&More (?Nothing ; c)) =
            (Leaf, c)
        unmarsh @a (&More (?(Just x) ; c)) =
            let (l, c) = unmarsh @a c
                (r, c) = unmarsh @a c
            in (Node l x r, c)

aTree : Tree Int
aTree = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)

_ = forkWith (marshall aTree) |> unmarshall |> print

leftoverTokens : Stream (Maybe Int) -> ()
leftoverTokens c = c |> select More |> send (Just 1) |> select More |> send (Just 2) |> select Done |> close

-- Ends with an error because the stream still offers More after the tree has been fully unmarshalled.
-- _ = forkWith (leftoverTokens) |> unmarshall |> print

truncatedTree : Stream (Maybe Int) -> ()
truncatedTree c = c |> select More |> send (Just 1) |> select Done |> close

-- Ends with an error
-- _ = forkWith (truncatedTree) |> unmarshall |> print