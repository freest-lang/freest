module ArrowLinType where 

type Arrow = Int -1-> Bool

isTen : Arrow
isTen x = x == 10

main : Bool
main = isTen 10
