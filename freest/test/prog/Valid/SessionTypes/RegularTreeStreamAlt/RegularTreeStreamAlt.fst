module RegularTreeStreamAlt where

-- Represents a classical binary tree (Node LeftTree RightTree)
type Tree : *T
data Tree = Leaf | Node Int Tree Tree

-- Example of the following Tree:
--               1
--        2            6
--    8      3            7
--         5   4
aTree : Tree
aTree = Node 1 (Node 2 (Node 8 Leaf Leaf) (Node 3 (Node 5 Leaf Leaf) (Node 4 Leaf Leaf))) (Node 6 Leaf (Node 7 Leaf Leaf))


-- Represents a Stack of Tree
type TreeStack : *T
data TreeStack = Empty | Value Tree TreeStack

-- Push a Tree to the stack
stackPush : Tree -> TreeStack -> TreeStack
stackPush = Value

-- Pop the top Tree from the Stack (Leaf if empty)
stackPop : TreeStack -> (TreeStack, Tree)
stackPop ts =
  case ts of
    Empty      -> (ts, Leaf)
    Value t ts -> (ts, t)

-- Is the Stack empty
stackIsEmpty : TreeStack -> Bool
stackIsEmpty ts =
  case ts of
    Empty     -> True
    Value _ _ -> False

-- Size of the Stack
stackSize : TreeStack -> Int
stackSize ts =
  case ts of
    Empty      -> 0
    Value _ ts -> 1 + stackSize ts


-- Channel to send/receive a Tree. It is important that both sender and receiver
--  agree on an order to traverse the Tree.
--  (In our particular case we will use PREORDER - node, left, right)
type TreeC : 1C
type TreeC = +{ ValueC : !Int; TreeC
              , LeafC  : TreeC
              , FinishC: Close
              }


-- Sends a tree through a TreeC
sendTree : Tree -> TreeC -> TreeC
sendTree t c =
  case t of
    Leaf ->
      select LeafC c
    Node i lt rt ->
      sendTree rt c |> sendTree lt |> select ValueC |> send i

-- Generates an error with a given message if a given boolean is true
errorWhen : Bool -> String -> ()
errorWhen b s =
  if b
  then error s
  else ()

-- Receives a Tree from a TreeC
--  This function also serves as an abstraction to the TreeStack usage
receiveTree_ : TreeStack -> Dual TreeC -> Tree
receiveTree_ ts c =
  case c of
    &ValueC c ->
      let (i, c)   = receive c in
      errorWhen (stackIsEmpty ts) "Received Value without receiveing left AND right subtrees";
      let (ts, lt) = stackPop ts in
      errorWhen (stackIsEmpty ts) "Received Value without receiveing left OR right subtrees";
      let (ts, rt) = stackPop ts in
      let ts       = stackPush (Node i lt rt) ts in
      receiveTree_ ts c
    &LeafC c ->
      receiveTree_ (stackPush Leaf ts) c
    &FinishC  c ->
      wait c; 
      errorWhen (stackIsEmpty ts)  "Channel was closed without sending a Tree";
      errorWhen (stackSize ts > 1) "Channel was closed mid-stream or with leftover tree elements";
      snd $ stackPop ts

-- Facade function to receive a Tree through a channel
receiveTree : Dual TreeC -> Tree
receiveTree c = receiveTree_ Empty c 

-- Simple treeClient that sends a Tree through a TreeC
treeClient : TreeC -> ()
treeClient c = sendTree aTree c |> select FinishC |> close

-- ==== BAD CLIENTS ===
-- These are bad client implementations to test error situations

-- This bad client ends prematurely
badClientPrematureEnd : TreeC -> ()
badClientPrematureEnd c =
  select FinishC c |> close

-- This bad client send an extra Value -1
badClientSendExtraValue : TreeC -> ()
badClientSendExtraValue c =
  sendTree aTree c |> select ValueC |> send (-1) |> select FinishC |> close  
  -- Bad Code         ===========================

-- This bad client send an extra Leaf
badClientSendExtraLeaf : TreeC -> ()
badClientSendExtraLeaf c =
  sendTree aTree c |> select LeafC |> select FinishC |> close 
  -- Bad  Code         =============

-- This client does not send the right subtree
-- Sends a tree through a TreeC
-- !!! But forgets to send right subtree
badSendTree : Tree -> TreeC -> TreeC
badSendTree t c =
  case t of
    Leaf ->
      select LeafC c
    Node i lt rt ->
      send i $ select ValueC $ badSendTree lt c -- $ badSendTree rt c

badClientForgotRight: TreeC -> ()
badClientForgotRight c =
  badSendTree aTree c |> select FinishC |> close 
  -- Bad Code          ===========

-- This client only sends a value without sending leafs
badClientSendOnlyValue : TreeC -> ()
badClientSendOnlyValue c =
  select ValueC c |> send 1 |> select FinishC |> close

-- ==== MAIN ====
-- This main acts as the server that receives the Tree sent by a client
main : Tree
main =
  let (w, r) = channel @TreeC in
  fork #1 (\(_ : ()) -1-> treeClient w);
  --fork $ badClientPrematureEnd w;
  --fork $ badClientSendExtraValue w;
  --fork $ badClientSendExtraLeaf w;
  --fork $ badClientForgotRight w;
  --fork $ badClientSendOnlyValue w;
  receiveTree r