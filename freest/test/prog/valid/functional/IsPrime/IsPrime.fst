module IsPrime where

fact : Int -> Int
fact n = if n == 0 then 1 else n * fact (n - 1)

isPrime : Int -> Bool
isPrime x = rem (fact (x-1)) x == x-1

main : Bool
main = isPrime 17

