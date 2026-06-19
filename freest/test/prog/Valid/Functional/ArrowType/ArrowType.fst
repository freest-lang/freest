module ArrowType where

type Arrow : *T
type Arrow = Int -> Bool

is10 : Arrow
is10 x = x == 10

main : ()
main = print (is10 12 || is10 10)
