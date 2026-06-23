module IntList where

data IntList = Nil | Cons Int IntList

null' : IntList -> Bool
null' Nil        = True
null' (Cons x y) = False

main : ()
main = print (null' (Cons 5 (Cons 7 Nil)))
