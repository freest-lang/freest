module MultipleListTransformations where

type IntList : *T
data IntList = Nil | Cons Int IntList

-- sum' +
sum' : IntList -> Int
sum' l =
  case l of
    Nil -> 0
    Cons x y -> x + sum' y

toNegative : IntList -> IntList
toNegative l =
    case l of
        Nil -> Nil
        Cons x y -> Cons (-x) (toNegative y)

-- sumNegatives -
sumNegatives : IntList -> Int
sumNegatives l = sum' (toNegative l)

-- specInterchange (specific)
specInterchange : IntList -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> Int
specInterchange l f1 f2 = 
    case l of
        Nil -> 0
        Cons a b -> 
            case b of 
                Nil -> a
                Cons c d ->
                    specInterchange (Cons (f1 a c) d) f2 f1

-- repetidor
repetidor : Int -> Int -> IntList
repetidor i n =
    if i == 0 
        then Nil
        else Cons n (repetidor (i-1) n)

-- makeUntil
makeUntil : Int -> IntList
makeUntil i = if i == 0 then Nil else Cons i (makeUntil (i-1)) 

-- takeOutNumber
takeOutNumber : IntList -> Int -> IntList
takeOutNumber l n =
    case l of
        Nil -> Nil
        Cons x y ->
            if x == n
                then takeOutNumber y n
                else Cons x (takeOutNumber y n)

-- incrementList
incrementList : IntList -> Int -> IntList
incrementList l i =
    case l of
        Nil -> Nil
        Cons x y -> Cons (x+i) (incrementList y i)

-- multiplyList
multiplyList : IntList -> Int -> IntList
multiplyList l m =
    case l of
        Nil -> Nil
        Cons x y -> Cons (x*m) (multiplyList y m)

-- decrementList
decrementList : IntList -> Int -> IntList
decrementList l i =
    case l of
        Nil -> Nil
        Cons x y -> Cons (x-i) (decrementList y i)

-- divideList
divideList : IntList -> Int -> IntList
divideList l m =
    case l of
        Nil -> Nil
        Cons x y -> Cons (x/m) (divideList y m)

equalsList : IntList -> IntList -> Bool
equalsList l1 l2 =
    case l1 of
        Nil ->
            case l2 of
                Nil -> True
                Cons _ _ -> False
        Cons a b ->
            case l2 of
                Nil -> False
                Cons c d -> 
                    if a == c
                        then equalsList b d
                        else False

list1 : IntList
list1 = repetidor 10 2

list2 : IntList
list2 = makeUntil 10

main : ()
main = 
    let a = sum' list1 in
    let b = sumNegatives list1 in
    let c = specInterchange list1 (+) (-) in
    let d = specInterchange list1 (*) (div) in
    let e = takeOutNumber list2 10 in
    let f = decrementList (incrementList list1 1) 1 in
    let g = divideList (multiplyList list1 2) 2 in
    print (  (a == 10*2)
          && (b == 10*-2)
          && (c == 4)
          && (d == 4)
          && (equalsList (makeUntil 9) e)
          && (equalsList list1 f)
          && (equalsList list1 g)
          )

