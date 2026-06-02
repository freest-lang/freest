module LinArrowAsUn where

-- f takes as input an unrestricted function
f : (Int -> Int) -> Int -> Int
f g n = g n 

main : Int
main = f (\(n : Int) -1-> n + 10) 4 -- here it is given a linear one

-- since linear functions cannot be used unrestrictedly, an error should be thrown