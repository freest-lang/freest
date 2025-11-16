module WrongNumberOfFieldsInBranch where

f : &{A: Skip, B: Skip} -> Int
f c = case c of 
  &A _ -> 5
  &B _ -> 6
  &C _ -> 7

main : Int
main = 5
