module LambdaHO where

f : (Int -> Int) -> Int
f g = g (g 5)

main : Int
main = f (\x : Int -> x + 1)
