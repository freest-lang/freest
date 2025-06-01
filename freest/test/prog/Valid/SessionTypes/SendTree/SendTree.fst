-- {- |
-- Module      :  Exchange a binary tree on a channel
-- Description :  As in "Context-Free Session Types", ICFP'16
-- Copyright   :  (c) LASIGE and University of Lisbon, Portugal
-- Maintainer  :  balmeida@lasige.di.fc.ul.pt
-- -}

module SendTree where

type Tree : *T
data Tree = Leaf | Node Tree Int Tree

aTree : Tree
aTree = Node (Node Leaf 5 Leaf) 7 (Node (Node Leaf 11 Leaf) 9 (Node Leaf 15 Leaf))

type TreeChannel : 1C
type TreeChannel = TreeC ; Wait

type TreeC : 1S
type TreeC = &{
  LeafC: Skip,
  NodeC: TreeC ; ?Int ; TreeC
 }

read : forall (a : 1S). TreeC ; a -> (Tree, a)
read @a (&LeafC c) = (Leaf, c)
read @a (&NodeC c) =
  let (l, c) = read @(?Int; TreeC; a) c in
  let (x, c) = receive @Int @(TreeC; a) c in
  let (r, c) = read @a c in
  (Node l x r, c)

readTree : TreeChannel -> Tree
readTree r = 
  let (tree, r) = read @Wait r in 
  let _ = wait r in
  tree

write : forall (a : 1S). Tree -> Dual TreeC ; a -> a
write @a Leaf c = select LeafC c
write @a (Node l x r) c = 
  write @a r (send @Int x @(Dual TreeC; a) (write @(!Int;Dual TreeC;a) l (select NodeC c)))

writeTree : Tree -> Dual TreeChannel -> ()
writeTree tree writer =
  close (write @Close tree writer)

main : Tree
main =
  readTree (forkWith @TreeChannel @() (writeTree aTree))
