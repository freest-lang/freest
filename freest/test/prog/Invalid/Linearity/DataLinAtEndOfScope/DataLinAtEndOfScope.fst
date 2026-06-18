module DataLinAtEndOfScope where

type T : 1T
data T = C (Int -1-> Int)

f : Int -1-> Int
f x = x

main : Int
main = case C f of C x -> 5 
