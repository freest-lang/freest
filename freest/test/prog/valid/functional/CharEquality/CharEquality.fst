module CharEq where

equalChars : Char -> Char -> Bool
equalChars c1 c2 = ord c1 == ord c2

main : Bool
main = equalChars 'a' 'a'

