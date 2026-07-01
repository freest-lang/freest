module HTree where

type HTree : 1S
type HTree = +{Node: HTree; !type a. !a; HTree, Empty: Skip}

client : HTree -> Skip
client c =              -- (Node Empty True (Node Empty 25 Empty))
  c |> select Node
    |> select Empty
    |> sendType @Bool
    |> send True
    |> select Node
    |> select Empty
    |> sendType @Int
    |> send 25
    |> select Empty

server : forall (a : 1S) -> Dual HTree; a -> a
server @a (&Node c) =
    let (@(b : *T), c) = c |> server |> receiveType
        (x , c) = receive c
    in server c
server @a (&Empty c) = c