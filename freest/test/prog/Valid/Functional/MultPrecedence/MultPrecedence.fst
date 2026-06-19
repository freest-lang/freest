module MultPrecedence where

precedence : Int
precedence = 2 + 3 * 4 + 5

main : ()
main = print precedence
