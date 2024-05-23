module ParensPrecedence where

precedence : Int
precedence = ((2 + 3) * 4) * (1 + 5)

main : Int
main = precedence

