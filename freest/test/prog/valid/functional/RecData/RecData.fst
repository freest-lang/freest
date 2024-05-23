module RecData where

data T  = C T

-- Not bound to terminate
main : T
main = C main

-- main : Int
-- main = 2
