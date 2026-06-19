module MultDivPrecedence where

precedence : Int
precedence = div 6 2 * (1 + 2)

main : ()
main = print precedence