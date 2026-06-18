module ListEquality where

data List = Nil | Cons Int List

-- A list: [2,3,4,5]
aList1 : List
aList1 = (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))

-- A list: [1,2,3,5]
aList3 : List
aList3 = (Cons 1 (Cons 2 (Cons 3 (Cons 5 Nil))))


equalList : List -> List -> Bool
equalList xs ys =
  case xs of
    Cons x xs ->
      case ys of
        Nil -> False
        Cons y ys -> x == y && equalList xs ys
    Nil ->
      case ys of
        Nil  -> True
        Cons _ _ -> False

equalList' : List -> List -> Bool
equalList' Nil         Nil         = True
equalList' (Cons _ __) Nil         = False
equalList' Nil         (Cons _ __) = False
equalList' (Cons x xs) (Cons y ys) = x == y && equalList xs ys

main : Bool
main = equalList aList1 aList3
