{- |
Module      : SystemFBooleans
Description : Examples from TAPL, Chapter 23, Universal Types
Copyright   : (c) Vasco T. Vasconcelos, 31 dec 2020

Church Encoding _ Boolean Values
-}

module SystemFBooleans where

type Bool' : *T
type Bool' = forall (b : *T). b -> b -> b

trueC, falseC : Bool'

trueC  = \@(a : *T) -> \(t : a) -> \(f : a) -> t

falseC = \@(a : *T) -> \(t : a) -> \(f : a) -> f

notC : Bool' -> Bool'
notC = \(b : Bool') -> \@(a : *T) -> \(t : a) -> \(f : a) -> b @a f t

-- Abbreviated versions of the above

type Bool'' : *T -> *T
type Bool'' b = b -> b -> b

trueC', falseC': forall (b : *T). Bool'' b

trueC'  @b t _ = t

falseC' @b _ f = f

notC' : forall (b : *T). Bool'' b -> Bool'' b
notC' @b b = \(t : b) (f : b) -> b f t

-- Destructor

cond : forall (a : *T) . Bool' -> a -> a -> a
cond @a b e1 e2 = b @a e1 e2

-- Boolean ops based on the conditional

notC'' : Bool' -> Bool'
notC'' b = cond  @Bool' b falseC trueC

orC, andC : Bool' -> Bool' -> Bool'
orC b1 b2 = cond  @Bool' b1 trueC b2

andC b1 b2 = cond  @Bool' b1 b2 falseC

-- Testing

toBool : Bool' -> Bool
toBool b = b  @Bool True False

toBit : Bool' -> Int
toBit b = b  @Int 1 0

ifInt : Bool' -> Int -> Int -> Int
ifInt = cond  @Int

-- main : Int
-- main = ifInt (notC trueC) 1 2

main : Bool
main = toBool $ andC (orC falseC trueC) (notC falseC)
