module FunLinearity where

f : Int -> Int
f x = 2 * x

g : (Int 1-> Int) -> Int
g f = f (f 5)

main : Int
main = g 
