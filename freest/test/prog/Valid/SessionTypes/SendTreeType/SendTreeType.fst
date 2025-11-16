{- |
Module      :  Exchange a binary tree on a channel
Description :  As in "Context-Free Session Types", ICFP'16
Copyright   :  (c) LASIGE and University of Lisbon, Portugal
Maintainer  :  balmeida@lasige.di.fc.ul.pt
-}

module SendTreeType where

type Tree : *T
data Tree = Leaf | Node Int Tree Tree

type TreeChannel : 1S
type TreeChannel = +{
  LeafC: Skip,
  NodeC: !Int ; TreeChannel ; TreeChannel
 }

write : forall (a : 1S). Tree -> TreeChannel; a -> a
write @a t c =
  case t of
    Leaf ->
      select LeafC c
    Node x l r ->
      select NodeC c
      |> send x
      |> write  @(TreeChannel ; a) l
      |> write @a r

read : forall (a : 1S). Dual TreeChannel; a -> (Tree, a)
read @a c =
  case c of
    &LeafC c ->
      (Leaf, c)
    &NodeC c ->
      let (x, c) = receive c in
      let (left, c) = read  @(Dual TreeChannel; a) c in
      let (right, c) = read  @a c in
      (Node x left right, c)

aTree, main : Tree

aTree = Node 7 (Node 5 Leaf Leaf) (Node 9 (Node 11 Leaf Leaf) (Node 15 Leaf Leaf))

main =
  let (writer, reader) = channel @(TreeChannel;Close) in
  fork  @() (\(_ : ()) 1-> write  @Close aTree writer |> close);
  let (tree, reader) = read  @Wait reader in 
  wait reader;
  tree

