module Scope where

main : ()
main = let x = 5 in print ((let x = True in 7) + x)
