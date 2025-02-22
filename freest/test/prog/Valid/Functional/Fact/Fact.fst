module Fact where

fact : Int -> Int
fact n = if n == 0 then 1 else n * fact (n - 1)

main : Int
main = fact 12

