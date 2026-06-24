module RegularTreeStream where

-- Integer trees

type Tree : *T
data Tree = Leaf | Node Int Tree Tree | Error

-- Example:
--               1
--        2            6
--    8      3            7
--         5   4
aTree : Tree
aTree = Node 1 (Node 2 (Node 8 Leaf 
                               Leaf) 
                       (Node 3 (Node 5 Leaf 
                                       Leaf) 
                               (Node 4 Leaf 
                                       Leaf))) 
               (Node 6 Leaf 
                       (Node 7 Leaf 
                               Leaf))

getFromSingleton : [Tree] -> Tree
getFromSingleton [x] = x
getFromSingleton []  = putStrLn "Error: Premature EndOfStream"; Error
getFromSingleton _   = putStrLn "Error: Extraneous elements in the stream after reading a full tree"; Error

getTwo : [Tree] -> ([Tree], (Tree, Tree))
getTwo (l :: r :: xs) = (xs, (l, r))
getTwo []             = putStrLn "Error: Empty stack on right subtree"; 
                        ([] @Tree, (Error, Error))
getTwo [l]            = putStrLn "Error: Empty stack on left subtree"; 
                        ([] @Tree, (Error, l))

-- Streams
type Stream : 1C
type Stream = +{
    NodeC: !Int ; Stream
  , LeafC: Stream
  , EndOfStreamC: Close
  }

-- Writing trees on channels

streamTree : Tree -> Stream -> Stream
streamTree Error        c = select LeafC c
streamTree Leaf         c = select LeafC c
streamTree (Node x l r) c = 
  c |> streamTree l |> streamTree r |> select NodeC |> send x

sendTree : Tree -> Stream -> ()
sendTree t c = c |> streamTree t |> select EndOfStreamC |> close

-- Reading trees from channels

recTree : [Tree] -> Dual Stream -> Tree
recTree xs (&EndOfStreamC c) = wait c ; getFromSingleton xs
recTree xs (&LeafC        c) = recTree (Leaf       :: xs) c
recTree ts (&NodeC        c) = recTree (Node x l r :: ts) c
  where (ts, (l, r)) = getTwo ts
        (x, c) = receive c  

receiveTree : Dual Stream -> Tree
receiveTree = recTree ([] @Tree)

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
  -- fork (\(_ : ()) -1-> sendTree aTree w);   -- No error
  fork (\_ -1-> writeNothing w);             -- Error: Premature EndOfStream
  -- fork (\(_ : ()) -1-> writeTooMuch w);      -- Error: Extraneous elements in the stream after reading a full tree
  -- fork (\(_ : ()) -1-> writeRootTreeOnly w); -- "Error: Empty stack on right subtree"
  -- fork (\(_ : ()) -1-> writeLeftTreeOnly w); -- "Error: Empty stack on left subtree",
  receiveTree r
  -- let t = receiveTree r in repeat 10000 (\(_ : ()) -> ()) ; t
