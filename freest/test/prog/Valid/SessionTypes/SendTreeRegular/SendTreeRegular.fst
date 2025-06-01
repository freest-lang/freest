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

aTree : Tree
aTree = Node (Node Leaf 5 Leaf) 7 (Node (Node Leaf 11 Leaf) 9 (Node Leaf 15 Leaf))

type TreeC : 1C
type TreeC = &{
  LeafC: Wait,
  NodeC: ?TreeC ; ?Int ; ?TreeC ; Wait
 }

read : TreeC -> Tree
read (&LeafC c) = (;) @() @Tree (wait c) Leaf
read (&NodeC c) =
  let (l, c) = receive @TreeC @(?Int;?TreeC;Wait) c in
  let (x, c) = receive @Int @(?TreeC;Wait) c in
  let  r     = receiveAndWait @TreeC c in 
  Node (read l) x (read r)

write : Tree -> Dual TreeC 1-> ()
write Leaf c = close (select LeafC c)
write (Node l x r) c =
  close 
    (send @TreeC (forkWith @TreeC @() (write r)) @Close
      (send @Int x @(!TreeC;Close)
        (send @TreeC (forkWith @TreeC @() (write l)) @(!Int;!TreeC;Close)
          (select NodeC c))))

main : Tree
main =
  read (forkWith @TreeC @() (write aTree))
