module LambdaHO where

f : (Int -> Int) -> Int
f g = g (g 5)

main : ()
main = print (f (\x -> x + 1))
