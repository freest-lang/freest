module RecPair where

type InfinitePair : *T -> *T
type InfinitePair a = (a, Int)

f : Int -> InfinitePair
f x = (f x, x + 1)

main : Int
main = 5
