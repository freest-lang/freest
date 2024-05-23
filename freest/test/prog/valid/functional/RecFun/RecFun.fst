module RecFun where

f : rec a. (Int -> a)
f x = f x

main : Int
main = 5
