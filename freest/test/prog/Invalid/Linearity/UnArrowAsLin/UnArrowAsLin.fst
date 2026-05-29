module UnArrowAsLin where

-- f takes as input a linear function
f : (Int -1-> Int) -> Int -1-> Int
f g n = g n 

main : Int
main = f (\(n : Int) -*-> n + 10) 4 -- here it is given an unrestricted one
