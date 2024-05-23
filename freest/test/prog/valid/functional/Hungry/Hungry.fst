module Hungry where

-- Types and Programming Languages, Benjamin Pierce, Page 270

-- type Hungry = rec a:TU. Int -> a
-- type Hungry = rec a:TU. (Int -> a) 

-- f : Int -> rec a. Hungry  
f : Int -> rec a . (Int -> a)
f n = f

g : rec a . (Int -> a)
g = f 0 1 2 3 4 5

main : Int
main = 5
