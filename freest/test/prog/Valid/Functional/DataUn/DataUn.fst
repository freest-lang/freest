module DataUn where

data T = C (Int -> Int)

f : Int -> Int
f x = x

main : ()
main = case C f of C g -> print (g (g 5))
