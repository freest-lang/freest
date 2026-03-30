module DataTypeMismatch where

type IntList : *T
data IntList = Nil | Cons Int IntList

main : Bool
main = Cons 4 Nil
