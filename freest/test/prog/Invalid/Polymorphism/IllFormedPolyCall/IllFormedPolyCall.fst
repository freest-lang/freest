module IllFormedPolyCall where

type Tree : *T
data Tree = Empty | Node Int Tree Tree

type TreeC : 1S
type TreeC = +{EmptyC: Skip, NodeC: !Int; TreeC; TreeC}

sendTree : forall (a : 1S). Tree -> TreeC; a -> a
sendTree @a t c =
  case t of
    Empty ->
      select EmptyC c
    Node x l r ->
      let c = select NodeC c in
      let c = send x c in
      let c = sendTree  @(TreeC; x) l c in
      let c = sendTree  @a r c in
      c

