module LinUsedTwice where

f : Int 1-> Int
f x = x

main : Int
main =  f (f 5)