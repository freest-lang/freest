{- |
Module      : SystemFPairs
Description : Pairs in System F
Copyright   : (c) Vasco T. Vasconcelos, 12 nov 2021

Church Encoding _ Sums
as per Practical Foundations for Programming Languages, Robert Harper, 2nd edition, page 141
-}

-- CANNOT INFER (id @T) as argument

module SystemFSums where

type Sum : *T -> *T -> *T
type Sum a b = forall (c : *T) -> (a -> c) -> (b -> c) -> c

inl : forall (a : *T) (b : *T) -> a -> Sum a b
inl @a @b e = \@(c : *T) (x : a -> c) (_ : b -> c) -> x e

inr : forall (a : *T) (b : *T) -> b -> Sum a b
inr @a @b e = \@(c : *T) (_ : a -> c) (y : b -> c) -> y e

cases : forall (a : *T) (b : *T) (c : *T) -> Sum a b -> (a -> c) -> (b -> c) -> c
cases @a @b @c e cl cr = e  @c cl cr

fromL : forall (a : *T) (b : *T) -> Sum a b -> a -> a
fromL @a @b l v = cases  @a @b @a l (id  @a) (\(_ : b) -> v)

fromR : forall (a : *T) (b : *T) -> Sum a b -> b -> b
fromR @a @b r v = cases  @a @b @b r (\(_ : a) -> v) (id  @b)

-- Examples

-- inject an Int in a Int+Bool sum
inInt : Int -> Sum Int Bool
inInt n = inl  @Int  @Bool n

-- inject a Bool in a Int+Bool sum
inBool : Bool -> Sum Int Bool
inBool b = inr  @Int  @Bool b

-- convert a Int+Bool sum into an Int
main, toInt : Int

main = fromL  @Int @Bool (inInt 324) 0

-- same w/o using fromL
toInt = cases  @Int @Bool @Int (inInt 324) (id  @Int) (\(_ : Bool) -> 0)

-- convert a Int+Bool sum into a Bool
main', toBool : Bool

main' = fromR  @Int @Bool (inBool True) False

toBool = cases  @Int @Bool @Bool (inBool True) (\(_ : Int) -> False) (id  @Bool)


