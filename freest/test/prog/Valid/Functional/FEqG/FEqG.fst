module FEqG where

g : Int -> Int
g x = x

f : Int -> Int
f = g

main : ()
main = print (f 5)