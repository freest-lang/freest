-- {- |
-- Module      :  Exchange a binary tree on a channel
-- Description :  As in "Context-Free Session Types", ICFP'16
-- Copyright   :  (c) LASIGE and University of Lisbon, Portugal
-- Maintainer  :  balmeida@lasige.di.fc.ul.pt
-- -}

module SendTree where

data Tree = Leaf | Node Tree Int Tree

aTree : Tree
aTree = Node (Node Leaf 5 Leaf) 7 (Node (Node Leaf 11 Leaf) 9 (Node Leaf 15 Leaf))

type TreeChannel = TreeC ; Wait

type TreeC = &{
  LeafC: Skip,
  NodeC: TreeC ; ?Int ; TreeC
 }

read : TreeC ; a -> (Tree, a)
read (LeafC c) = (Leaf, c)
read (NodeC c) =
  let (l, c) = read @(?Int ; TreeC ; a) c in
  let (x, c) = receive c in
  let (r, c) = read @a c in
  (Node l x r, c)

readTree : TreeChannel -> Tree
readTree r = 
  let (tree, r) = read @Wait r in 
  wait r;
  tree

write : Tree -> Dual TreeC ; a -> a
write Leaf c = select LeafC c
write (Node l x r) c = 
  c |> select NodeC
    |> write @(!Int;Dual TreeC;a) l
    |> send x
    |> write @a r

writeTree : Tree -> Dual TreeChannel -> ()
writeTree tree writer =
  write @Close tree writer |> close

main : Tree
main =
  forkWith @TreeChannel @() (writeTree aTree) |>
  readTree
