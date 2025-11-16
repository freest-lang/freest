module DataUn where

type T : *T
data T = C (Int -> Int)

f : Int -> Int
f x = x

main : Int
main = case C f of C g -> g (g 5)
