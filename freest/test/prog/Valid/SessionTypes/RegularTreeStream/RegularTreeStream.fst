module RegularTreeStream where

-- Integer trees

data Tree = Leaf | Node Int Tree Tree | Error

-- Example:
--               1
--        2            6
--    8      3            7
--         5   4
aTree : Tree
aTree = Node 1 (Node 2 (Node 8 Leaf Leaf) (Node 3 (Node 5 Leaf Leaf) (Node 4 Leaf Leaf))) (Node 6 Leaf (Node 7 Leaf Leaf))

-- Tree lists and operations on Lists

data List = Nil | Cons Tree List

null : List -> Bool
null Nil = True
null (Cons _ _) = False

head : List -> Tree
head (Cons x _) = x

tail : List -> List
tail (Cons _ xs) = xs

getFromSingleton : List -> Tree
getFromSingleton (Cons x Nil) = x
getFromSingleton Nil = print @String "Error: Premature EndOfStream" ; Error
getFromSingleton _ = print @String "Error: Extraneous elements in the stream after reading a full tree" ; Error

getTwo : List -> (List, (Tree, Tree))
getTwo (Cons left (Cons right xs)) = (xs, (left, right))
getTwo Nil = print @String "Error: Empty stack on right subtree" ; (Nil, (Error, Error))
getTwo (Cons left Nil) = print @String "Error: Empty stack on left subtree" ; (Nil, (Error, left))

-- Streams

type Stream = +{
    NodeC: !Int ; Stream
  , LeafC: Stream
  , EndOfStreamC: Close
  }

-- Writing trees on channels

streamTree : Tree -> Stream -> Stream
streamTree Leaf c = select LeafC c
streamTree (Node x l r) c = send x $ select NodeC $ streamTree r $ streamTree l c
streamTree Error c = select LeafC c

sendTree : Tree -> Stream -> ()
sendTree t c = c |> streamTree t |> select EndOfStreamC |> close

-- Reading trees from channels

recTree : List -> Dual Stream -> Tree
recTree xs (NodeC c) =
  let (xs, p) = getTwo xs in
  let (left, right) = p in
  let (root, c) = receive c in
  recTree (Cons (Node root left right) xs) c
recTree xs (LeafC c) =
  recTree (Cons Leaf xs) c
recTree xs (EndOfStreamC c) =
  wait c ; getFromSingleton xs

receiveTree : Dual Stream -> Tree
receiveTree = recTree Nil

-- Babdly behaving writers

writeNothing, writeTooMuch, writeRootTreeOnly, writeLeftTreeOnly : Stream -> ()
writeNothing c =
  c |> select EndOfStreamC |> close

writeTooMuch c =
 c |>  select LeafC |> select LeafC |> select EndOfStreamC |> close

writeRootTreeOnly c =
  c |> select NodeC |> send 5 |> select EndOfStreamC |> close

writeLeftTreeOnly c =
  c|> select LeafC |> select NodeC |> send 5 |> select EndOfStreamC |> close

-- Go!

main : Tree
main =
  let (w, r) = channel @(Stream ; Close) in
  -- fork @()  (\_:() 1-> sendTree aTree w);   -- No error
  fork @() (\_:() 1-> writeNothing w) ;      -- Error: Premature EndOfStream
  -- fork @() (\_:() 1-> writeTooMuch w);      -- Error: Extraneous elements in the stream after reading a full tree
  -- fork @() (\_:() 1-> writeRootTreeOnly w); -- "Error: Empty stack on right subtree"
  -- fork @() (\_:() 1-> writeLeftTreeOnly w); -- "Error: Empty stack on left subtree",
  receiveTree r
  -- let t = receiveTree r in repeat @() 10000 (\_:() -> ()) ; t
