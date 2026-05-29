module Ordering where

{- |
Module      :  Ordering
Description :  Server that orders lists and returns them
Copyright   :  (c) Diogo Barros

This example shows a server that receives a list, lets the user choose which
order to use in quicksort and returns the ordered list.

-}

-- ==================== Structures ====================

type IntList : *T
data IntList = Nil | Cons Int IntList

type OrderingChannel : 1S
type OrderingChannel = +{Vals: !Int; OrderingChannel; ?Int, Asc: Skip, Desc: Skip}

-- ==================== QUICKSORT ====================

-- quicksort option to sort by ascending or descending
asc, desc : Int -> Int -> Bool
asc x i = x < i
desc x i = not (asc x i)

-- Divides a list into lesser and greater or equal,given a pivot
quicksortDivide' : Int -> IntList -> (IntList, IntList) -> (Int -> Int -> Bool) -> (IntList, IntList)
quicksortDivide' i list d direction =
  let (smaller, greater) = d in
  case list of
    Nil -> (smaller, greater)
    Cons x xs -> if direction x i
                 then quicksortDivide' i xs (Cons x smaller, greater) direction
                 else quicksortDivide' i xs (smaller, Cons x greater) direction

-- Facade function to quicksortDivide'
quicksortDivide : Int -> IntList -> (Int -> Int -> Bool) -> (IntList, IntList)
quicksortDivide i list direction = quicksortDivide' i list (Nil, Nil) direction

-- Appends two lists
listAppend : IntList -> IntList -> IntList
listAppend l ll =
  case l of
    Nil -> ll
    Cons x xs -> Cons x (listAppend xs ll)

-- Translated from Haskell code at learnyouahaskell.com/recursion
--   The function it receives determines which order it sorts,
--   ascending or descending
quicksort : IntList -> (Int -> Int -> Bool) -> IntList
quicksort list direction =
  case list of
    Nil -> Nil
    Cons x xs ->
      let (smaller, greater) = quicksortDivide x xs direction in
      listAppend (quicksort smaller direction) (Cons x (quicksort greater direction))

-- ==================== Server ====================

-- Server function
--   This server sends the list reversed
orderedServer : forall (a : 1S) -> (Dual OrderingChannel; a) -> IntList -1-> (IntList, a)
orderedServer @a c list =
  case c of
    &Vals c ->
      let (x, c)  = receive c in
      let (list, c) = orderedServer c (Cons x list) in
      case list of
        Cons y ys ->
          let c = send y c in
          (ys, c)
        -- Nil is never reached
    -- Quicksorts with descending to send it reversed
    &Asc  c ->
      (quicksort list (desc), c)
    -- Quicksorts with ascending to send it reversed
    &Desc c ->
      (quicksort list (asc), c)

-- Facade function to initialize server with an empty list
initOrderedServer : (Dual OrderingChannel; Wait) -> ()
initOrderedServer c =
  let (_, c) = orderedServer c Nil in
  wait c

-- ==================== Client ====================

-- Function to send a list and receive it ordered
--  direction : Bool - is used to determine if Asc(True) or
--                     Desc(False) is selected
order : forall (a : 1S) -> OrderingChannel; a -> IntList -1-> Bool -1-> (a, IntList)
order @a c sList direction =
  case sList of
    Nil -> if direction
           then (select Asc c , Nil)
           else (select Desc c, Nil)
    Cons x xs ->
      let c          = select Vals c in
      let c          = send x c in
      let (c, rList) = order c xs direction in
      let (y, c)     = receive c in
      (c, Cons y rList)

-- Mock list 
aList : IntList
aList = Cons 4 (Cons 1 (Cons 3 (Cons 2 Nil)))

-- Simple clients using Asc or Desc options
ascClient, descClient : (OrderingChannel; Close )-> IntList

ascClient c =
  let (c, rList) = order c aList True in
  close c;
  rList

descClient c =
  let (c, rList) = order c aList False in
  close c;
  rList

-- ==================== Main ====================

main : IntList
main =
  let (w, r) = channel @(OrderingChannel; Close) in
  let _      = fork (\(_ : ()) -1-> initOrderedServer r) in
  descClient w
  --ascClient w
