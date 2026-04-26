{- |
Module      :  LazyTreeTraversal
Description :  Computes the product of the values in a tree
Copyright   :  (c) Bernardo Almeida, Andreia Mordido, Vasco T. Vasconcelos

The example is from Thiemann and Vasconcelos: "Context-Free Session
Types" (listing 4)

The server computes the product of the values in a tree; explicitly
request the values; stop as soon a zero is received.

The client sends the tree as requested by the server.

The type describing this interaction is mutually recursive. The type
described by XploreNodeChan is tail-recursive like a regular session
type, but XploreTreeChan is not since its invocations are intertwined
with XploreNodeChan (adapted from the paper).

-}

module LazyTreeTraversal where

type Tree : *T
data Tree = Leaf | Node Int Tree Tree

type XploreTreeChan : 1S
type XploreTreeChan = +{LeafC: Skip,
                       NodeC: XploreNodeChan}

type XploreNodeChan : 1S
type XploreNodeChan = &{
   Value : !Int;XploreNodeChan ,
   Left : XploreTreeChan ; XploreNodeChan ,
   Right : XploreTreeChan ; XploreNodeChan ,
   Exit : Skip
 }

-- The client. Send the tree as requested by the server.
mutual
  exploreTree : forall (a : 1S). XploreTreeChan;a -> Tree 1-> a
  exploreTree @a c tree =
    case tree of
      Leaf ->
        select LeafC c
      Node x l r ->
        exploreNode (select NodeC c) x l r

  exploreNode : forall (a : 1S). XploreNodeChan;a -> Int 1-> Tree 1-> Tree 1-> a
  exploreNode @a c x l r =
    case c of
      &Value c ->
        exploreNode (send x c) x l r
      &Left c ->
        let c = exploreTree c l in
        exploreNode c x l r
      &Right c ->
        let c = exploreTree c r in
        exploreNode c x l r
      &Exit c ->
        c

-- The server. Compute the product of the values in a tree;
-- explicitely request the values; stop as soon a zero is received
mutual 
  server : forall (a : 1S). Dual XploreTreeChan ;a -> Int 1-> (a, Int)
  server @a c1 n =
    case c1 of
      &LeafC c1 -> (c1, n)
      &NodeC c1 -> serverNode c1 n

  serverNode : forall (a : 1S). Dual XploreNodeChan;a -> Int 1-> (a, Int)
  serverNode @a c n =
    let (m, c) = c |> select Value |> receive in
    if m == 0
    then (select Exit c, 0)
    else
      let c = select Left c in
      let (c, m) = server c (m * n) in
      let (c, k) = server (select Right c) m in
      (select Exit c, k)

aTree : Tree
aTree = Node 7 (Node 5 Leaf Leaf) (Node 9 (Node 11 Leaf Leaf) (Node 15 Leaf Leaf))

main : Int
main =
  let (writer, reader) = channel @(XploreTreeChan;Close) in
  fork (\(_:()) 1-> close (exploreTree writer aTree));
  let (reader, n) = server reader 1 in
  wait reader;
  n
