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

type Tree : *T
data Tree = Leaf | Node Int Tree Tree

type TreeC : 1S
type TreeC = +{LeafC: Skip, NodeC: !Int;TreeC;TreeC;?Int}

-- Note: we use the same constructors for the datatype and the channel, namely Leaf and Node

{-
  Writes a tree on a given channel;
  for each node in the tree reads an integer from the channel;
  returns a tree isomorphic to the input where each integer in nodes
  is read from the channel.
-}
transform : Tree -> TreeC ; a -> (Tree, a)
transform tree c =
  case tree of
    Leaf ->
      (Leaf, select LeafC c)
    Node x l r ->
      let c = select NodeC c in
      let c = send x c in
      let (l, c) = transform  @(TreeC ; ?Int ; a) l c in
      let (r, c) = transform  @(?Int ; a) r c in
      let (y, c) = receive c in
      (Node y l r, c)

{-
  Reads a tree from a given channel;
  writes back on the channel the sum of the elements in the tree;
  returns this sum.
-}
treeSum : Dual TreeC ; a -> (Int, a)
treeSum c =
  case c of
    LeafC c ->
     (0, c)
    NodeC c ->
      let (x, c) = receive c in
      let (l, c) = treeSum  @(Dual TreeC ; !Int ; a) c in
      let (r, c) = treeSum  @(!Int ; a) c in
      let c = send (x + l + r) c in
      (x + l + r, c)

aTree, main : Tree

aTree = Node 1 (Node 2 (Node 8 Leaf Leaf) (Node 3 (Node 5 Leaf Leaf) (Node 4 Leaf Leaf))) (Node 6 Leaf (Node 7 Leaf Leaf))

main =
  let (w, r) = channel @(TreeC;Wait) in
  fork @() (\_:()1-> close $ snd @Int @Close $ treeSum @Close r);
  let (t, w) = transform @Wait aTree w in
  wait w;
  t
