{- |
Module      :  TreeTransform
Description :  Serializes and tranforms a tree object on a channel
Copyright   :  (c) Bernardo Almeida, Andreia Mordido, Vasco T. Vasconcelos

The example is from Almeida, Mordido, and Vasconcelos, "FreeST:
Context-free Session Types in a Functional Language"

The example serializes a tree object on a channel. The aim is to
transform a tree by interacting with a remote server. The client
process streams a tree on a (single) channel. In addition, for each
node sent, an integer is received.  The server process reads a tree
from the other end of the channel and, for each node received, sends
back the sum of the integer values under (and including) that node.

-}

module TreeTransform where

type Tree : *T -> *T
data Tree a = Leaf | Node a (Tree a) (Tree a)

type TreeC : *T -> 1S
type TreeC a = +{LeafC: Skip, NodeC: !a; TreeC a; TreeC a; ?a}

-- Writes a tree on a given channel;
-- for each node in the tree reads an integer from the channel;
-- returns a tree isomorphic to the input where each integer in nodes
-- is read from the channel.
transform : forall (a : *T) (b : 1S) -> Tree a -> TreeC a; b -> (Tree a, b)
transform @a @b tree c =
  case tree of
    Leaf       -> (Leaf, select LeafC c)
    Node x l r -> (Node y l r, c)
      where c = select NodeC c
            c = send x c
            (l, c) = transform l c
            (r, c) = transform r c
            (y, c) = receive c

-- Reads a tree from a given channel;
-- writes back on the channel the sum of the elements in the tree;
-- returns this sum.
treeSum : forall (a : 1S) -> Dual (TreeC Int); a -> (Int, a)
treeSum @a c =
  case c of
    &LeafC c -> (0, c)
    &NodeC c -> (x + l + r, c)
      where (x, c) = receive c
            (l, c) = treeSum c
            (r, c) = treeSum c
            c = send (x + l + r) c

xs : Tree Int

xs = Node 1 (Node 2 (Node 8 Leaf
                            Leaf) 
                    (Node 3 (Node 5 Leaf 
                                    Leaf) 
                            (Node 4 Leaf 
                                    Leaf))) 
            (Node 6 Leaf 
                    (Node 7 Leaf 
                            Leaf))

main : ()
main =
  let (w, r) = channel @(TreeC Int; Wait) in
  fork (\_ -1-> treeSum r |> snd |> close);
  let (t, w) = transform xs w in
  wait w;
  print t
