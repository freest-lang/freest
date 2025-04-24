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

type TreeChannel = TreeC ; Close

type TreeC = +{
  LeafC: Skip,
  NodeC: TreeC ; !(?Int ; Close); TreeC
 }

-- Reading a channel end: consuming Dual TreeChannel

receiveCh : ?(?Int; Close) ; a -> (Int, a)
receiveCh c =
  let (r, c) = receive c in
  let x = receiveAndClose @(Int) r in
  (x, c)

read : Dual TreeC ; a -> (Tree, a)
read (LeafC c) = (Leaf, c)
read (NodeC c) =
  let (l, c) = read @(?(?Int ; Close) ; Dual TreeC ; a) c in
  let (x, c) = receiveCh @(Dual TreeC ; a) c in
  let (r, c) = read @a c in
  (Node l x r, c)

readTree : Dual TreeChannel -> Tree
readTree r = 
  let (tree, r) = read @Wait r in 
  wait r;
  tree


-- Writing a tree on a channel: consuming TreeChannel

data Tree = Leaf | Node Tree Int Tree

sendCh : Int -> !(?Int ; Close) ; a -> a
sendCh x c =
  let (r, w) = channel @(?Int ; Close) in
  let c = send r c in
  sendAndWait @(Int) x w ;
  c

write : Tree -> TreeC ; a -> a
write Leaf c = select LeafC c
write (Node l x r) c = 
  c |> select NodeC
    |> write @(!(?Int ; Close) ; TreeC ; a) l
    |> sendCh @(TreeC ; a) x
    |> write @a r

writeTree : Tree -> TreeChannel -> ()
writeTree tree writer =
  write @Close tree writer |> close

-- Go: transmit aTree

aTree : Tree
aTree = Node (Node Leaf 5 Leaf) 7 (Node (Node Leaf 11 Leaf) 9 (Node Leaf 15 Leaf))

main : Tree
main =
  forkWith @(Dual TreeChannel) @() (writeTree aTree) |>
  readTree
