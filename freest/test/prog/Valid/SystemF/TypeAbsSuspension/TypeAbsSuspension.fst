module TypeAbsSuspension where

g : Int -> forall (a:*T) -> Int
g x @a = g x @a

h : (forall (a:*T) -> Int) -> Int
h _ = 0

main : ()
main = print (h (g 5))