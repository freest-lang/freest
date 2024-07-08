module RecFun where

type RecFun = Int -> RecFun

f : RecFun
f x = f x

main : Int
main = 5
