module NTreeSend where

type Tree, TreeList : *T

-- Represents a n-Tree structure where each node has 0..n children.
data Tree = Empty | Node Int TreeList

-- List of Trees
data TreeList = Nil | Cons Tree TreeList

type TreeChannel, TreeListChannel : 1S

type TreeChannel = +{
  Node : !Int; TreeListChannel,
  Empty: Skip }

type TreeListChannel = +{
  Cons: TreeChannel; TreeListChannel,
  Nil : Skip }


-- ===== SENDING =====

mutual
  sendTree : forall (a : 1S). Tree -> TreeChannel;a -> a
  sendTree @a tree c =
    case tree of
      Empty ->
        select Empty c
      Node i children ->
        c |> select Node |> send i |> sendTreeList @a children

  sendTreeList : forall (a : 1S). TreeList -> TreeListChannel;a -> a
  sendTreeList @a list c =
    case list of
      Nil ->
        select Nil c
      Cons tree rest ->
        c |> select Cons |> sendTree @(TreeListChannel ; a) tree |> sendTreeList @a rest

-- ===== RECEIVING =====

mutual 
  receiveTree : forall (a : 1S). Dual TreeChannel;a -> (Tree, a)
  receiveTree @a c =
    case c of
      &Empty c ->
        (Empty, c)
      &Node c ->
        let (i, c)        = receive c in
        let (children, c) = receiveTreeList @a c in
        (Node i children, c)

  receiveTreeList : forall (a : 1S). Dual TreeListChannel;a -> (TreeList, a)
  receiveTreeList @a c =
    case c of
      &Nil c ->
        (Nil, c)
      &Cons c ->
        let (tree, c) = receiveTree @(Dual TreeListChannel ; a) c in
        let (rest, c) = receiveTreeList @a c in
        (Cons tree rest, c)

-- ===== MAIN =====

-- This definition represents the following Tree:
--                     0
--           1         2       3
--    7      8    6           4 5
--   13    11 20
aTree : Tree
aTree = Node 0 $ Cons (Node 1 $ Cons (Node 7 $ Cons (Node 13 Nil)
                                               Nil) $
                                Cons (Node 8 $ Cons (Node 11 Nil) $
                                               Cons (Node 20 Nil)
                                               Nil) $
                                Cons (Node 6 Nil)
                                Nil) $
                 Cons (Node 2 Nil) $
                 Cons (Node 3 $ Cons (Node 4 Nil) $
                                Cons (Node 5 Nil)
                                Nil)
                 Nil

clientSendTree : TreeChannel;Close -> ()
clientSendTree c = c |> sendTree @Close aTree |> close

main : Tree
main =
  let (client, server) = channel @(TreeChannel;Close) in
  fork (\(_ : ()) 1-> clientSendTree client);
  let (t, server) = receiveTree @Wait server in
  wait server;
  t
