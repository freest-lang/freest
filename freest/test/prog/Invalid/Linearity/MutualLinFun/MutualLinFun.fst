module MutualLinFun where

mutual
  f : Int -1-> Int
  f x = g x

  g : Int -1-> Int
  g x = f x
