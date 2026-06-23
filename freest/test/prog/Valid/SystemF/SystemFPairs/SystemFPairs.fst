{- |
Module      : SystemFPairs
Description : Pairs in System F
Copyright   : (c) Vasco T. Vasconcelos, 2 jan 2021

Church Encoding _ Pairs
-}

module SystemFPairs where

type Pair : *T -> *T -> *T
type Pair a b = forall (c : *T) -> (a -> b -> c) -> c

fst' : forall (a : *T) (b : *T) -> Pair a b -> a
fst' @a @b p = p  @a (\(x : a) (_ : b) -> x)

snd' : forall (a : *T) (b : *T) -> Pair a b -> b
snd' @a @b p = p  @b (\(_ : a) (y : b) -> y)

pair : forall (a : *T) (b : *T) -> a -> b -> Pair a b
pair @a @b x y = \@(c : *T) (z : a -> b -> c) -> z x y

intBoolPair : Int -> Bool -> Pair Int Bool
intBoolPair = pair  @Int @Bool

main : ()
main = print 
     $ snd'  @Int @Char 
     $ fst'  @(Pair Int Char)  @Bool
     $ pair  @(Pair Int Char)  @Bool (pair  @Int @Char 5 'c') False

