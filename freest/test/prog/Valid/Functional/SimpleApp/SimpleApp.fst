module SimpleApp where

half : Int -> Int
half x = div x 2

main : ()
main = print (half (2+2*3))
