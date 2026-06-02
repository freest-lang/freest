{- |
Module      : SystemFWarmUps
Description : Examples from TAPL, Chapter 23, Universal Types
Copyright   : (c) Vasco T. Vasconcelos, 31 dec 2020
-}

module SystemFWarmUps where

double, quadruple : forall (a : *T) -> (a -> a) -> a -> a

double = \@(a : *T) (f : a -> a) (x : a) -> f (f x)

quadruple = \@(a : *T) (f : a -> a) -> double @(a -> a) (double  @a) f

doubleInt : (Int -> Int) -> Int -> Int
doubleInt = double  @Int

doubleIntArrowInt : ((Int -> Int) -> (Int -> Int)) -> (Int -> Int) -> (Int -> Int)
doubleIntArrowInt = double  @(Int -> Int)

five, seven, thirteen : Int

five = id  @Int 5

seven = doubleInt (\(x : Int) -> x + 2) 3

thirteen = doubleIntArrowInt doubleInt (\(x : Int) -> x + 2) 5

main : Int
main = quadruple  @Int (\(x : Int) -> x + 2) 3
