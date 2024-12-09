module IntList where

type IntList : *T
data IntList = Nil | Cons Int IntList

null' : IntList -> Bool
null' Nil        = True
null' (Cons x y) = False

main : Bool
main = null' (Cons 5 (Cons 7 Nil))

