module TuplesAsPairsOfPairs where

t1 : (Int, (Int, Int))
t1 = (1,2,3)

t2 : (Int, Int, Int)
t2 = (1, (2, 3))

t3 : (Int, Int, (Int, Int))
t3 = (1, (2, 3, 4))

main : (Int, Int, Int)
main = (1, (2, 3))