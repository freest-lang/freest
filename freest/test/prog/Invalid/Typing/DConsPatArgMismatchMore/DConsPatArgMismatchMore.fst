module ManyArgsCaseCons where

data List = Cons Int List | Nil

moreThanOneElem : List -> Bool
moreThanOneElem l =
  case l of
    Nil -> False
    Cons i k z -> True


main : Bool
main = moreThanOneElem (Cons 2 (Cons 2 Nil))
