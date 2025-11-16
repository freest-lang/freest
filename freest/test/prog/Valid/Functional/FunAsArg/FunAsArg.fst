module FunAsArg where

f1 : Int -> (Int -> Int) -> Int
f1 x f = f x 

f2 : Int -> Int
f2 x = 20 + x

main : Int
main = f1 3 f2
