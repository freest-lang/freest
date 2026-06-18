module RecPair where

type InfinitePair a = (InfinitePair a, Int)

f : Int -> InfinitePair Int
f x = (f x, x + 1)

main : Int
main = 5
