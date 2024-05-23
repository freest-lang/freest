module Scope where

main : Int
main = let x = 5 in (let x = True in 7) + x
