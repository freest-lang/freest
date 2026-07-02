module InferredDataKinds where

-- Datatype kinds are inferred with no signature: `Tree` as `*T -> *T`
-- (recursion alone does not force linearity), and the per-parameter annotation
-- `(a : 1T)` is honoured faithfully.
data Tree a = Leaf | Node a (Tree a) (Tree a)
data Box (a : 1T) = Box a

sumTree : Tree Int -> Int
sumTree t =
  case t of
    Leaf -> 0
    Node x l r -> x + sumTree l + sumTree r

unbox : forall a -> Box a -> a
unbox @a b = case b of Box x -> x

main : ()
main = print (sumTree (Node 1 (Node 2 Leaf Leaf) Leaf) + unbox @Int (Box 5))
