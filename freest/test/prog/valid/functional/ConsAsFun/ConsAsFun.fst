module ConsAsFun where

type Tree : *T
data Tree = Node Int Tree Tree | Leaf

f : (Int -> Tree -> Tree -> Tree) -> Tree
f g = g 5 Leaf Leaf

main : Tree
main = f Node
