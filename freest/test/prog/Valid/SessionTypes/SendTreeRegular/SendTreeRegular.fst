{- |
Module      : Exchange a binary tree on a channel
Description : Uses regular, higher-order, channels,
              rather than first-order, context-free
Copyright   : (c) LASIGE and University of Lisbon, Portugal
Maintainer  : vmavsconcelos@ciencias.ulisboa.pt
-}

module SendTreeRegular where

type Tree : *T
data Tree = Leaf | Node Tree Int Tree

type TreeC : 1C
type TreeC = &{ LeafC: Wait
              , NodeC: ?TreeC; ?Int; ?TreeC; Wait
              }

read : TreeC -> Tree
read (&LeafC c) = wait c; Leaf
read (&NodeC c) = Node (read l) x (read r)
  where (l, c) = receive c
        (x, c) = receive c
        r     = receiveAndWait c 

write : Tree -> Dual TreeC -> ()
write Leaf         c = c |> select LeafC |> close
write (Node l x r) c =
  c |> select NodeC
    |> send (forkWith #* (write l))
    |> send x
    |> send (forkWith #* (write r))
    |> close

main : Tree
main = forkWith #* (write xs) |> read
  where xs = Node (Node Leaf 
                        5 
                        Leaf) 
                  7 
                  (Node (Node Leaf 
                              11 
                              Leaf) 
                        9
                        (Node Leaf 
                              15 
                              Leaf))
