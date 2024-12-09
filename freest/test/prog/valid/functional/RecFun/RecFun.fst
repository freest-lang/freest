module RecFun where

type RecFun : *T
type RecFun = Int -> RecFun

f : RecFun
f x = f x

main : Int
main = 5
