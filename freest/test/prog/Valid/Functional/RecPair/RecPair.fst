module RecPair where

-- type InfinitePair : *T -> *T
type InfinitePair a = (InfinitePair a, Int)

f : Int -> InfinitePair Int
f x = (f x, x + 1)
