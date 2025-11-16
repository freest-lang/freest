module SendData where

-- TODO: what are we trying to test here?

type Tree : *T
data Tree = Leaf | Node Int Tree Tree

f : Char
f = send (Node 5 Leaf Leaf)
