{- |
Module      :  Exchange a binary tree on a channel, an HO version
Description :  The producer, rather than sending the integer directly on the
channel, introduces an indirection: sends a channel on with the integer shall be
sent.
Copyright   :  (c) LASIGE and University of Lisbon, Portugal
Maintainer  :  balmeida@lasige.di.fc.ul.pt
-}

module SendTreeHO where

-- The channel type, as seen from the producer side

type TreeChannel : 1C
type TreeChannel = TreeC ; Close

type TreeC : 1S
type TreeC = +{
  LeafC: Skip,
  NodeC: TreeC ; !(?Int ; Close); TreeC
 }

-- Reading a channel end: consuming Dual TreeChannel

receiveCh : forall (a : 1S). ?(?Int; Close) ; a -> (Int, a)
receiveCh @a c =
  let (r, c) = receive c in
  let x = receiveAndClose @Int r in
  (x, c)

read : forall (a : 1S). Dual TreeC ; a -> (Tree, a)
read @a (&LeafC c) = (Leaf, c)
read @a (&NodeC c) =
  let (l, c) = read @(?(?Int; Close); Dual TreeC; a) c in
  let (x, c) = receiveCh @(Dual TreeC; a) c in
  let (r, c) = read @a c in
  (Node l x r, c)

readTree : Dual TreeChannel -> Tree
readTree r = 
  let (tree, r) = read @Wait r in 
  wait r;
  tree

-- Writing a tree on a channel: consuming TreeChannel
type Tree : *T
data Tree = Leaf | Node Tree Int Tree

sendCh : forall (a : 1S). Int -> !(?Int ; Close) ; a -> a
sendCh @a x c =
  let (r, w) = channel @(?Int ; Close) in
  let c = send r c in
  sendAndWait @Int x w;
  c

write : Tree -> TreeC ; a -> a
write Leaf c = select LeafC c
write (Node l x r) c = 
  c |> select NodeC
    |> write @(!(?Int; Close); TreeC; a) l
    |> sendCh @(TreeC; a) x
    |> write @a r

writeTree : Tree -> TreeChannel -> ()
writeTree tree writer =
  writer |> write @Close tree |> close

-- Go: transmit aTree

aTree : Tree
aTree = Node (Node Leaf 5 Leaf) 7 (Node (Node Leaf 11 Leaf) 9 (Node Leaf 15 Leaf))

main : Tree
main =
  forkWith @(Dual TreeChannel) @() (writeTree aTree)
    |> readTree