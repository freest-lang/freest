{- |
Module      : SystemFNats
Description : Examples from TAPL, Chapter 23, Universal Types
Copyright   : (c) Vasco T. Vasconcelos, 31 dec 2020

Church Encoding _ Natural Numbers
-}

module SystemFNats where

type Nat : *T
type Nat = forall (a : *T) -> (a -> a) -> a -> a

zero : Nat 
zero = \@(a : *T) (s : a -> a) (z : a) -> z

succ', square : Nat -> Nat
succ' n = \@(a : *T) (s : a -> a) (z : a) -> s (n @a s z)

square n = \@(a : *T) (s : a -> a) (z : a) -> n  @a (n  @a s) z

plus, plus', times, expr : Nat -> Nat -> Nat
plus m n = m  @Nat succ' n

plus' m n = \@(a : *T) (s : a -> a) (z : a) -> m  @a s (n  @a s z)

times m n = \@(a : *T) (s : a -> a) -> n  @a (m  @a s)

expr m n = \@(a : *T) (f : a -> a) -> n  @(a -> a) (m  @a) f

isZero : Nat -> Bool
isZero n = n  @Bool (\(_ : Bool) -> False) True

-- Pairs of natural numbers for the predecessor

type Pair : *T
type Pair = (Nat -> Nat -> Nat) -> Nat

fst', snd' : Pair -> Nat
fst' p = p (\(m : Nat) (_ : Nat) -> m)

snd' p = p (\(_ : Nat) (n : Nat) -> n)

pair : Nat -> Nat -> Pair
pair m n = \(z : Nat -> Nat -> Nat) -> z m n

shift : Pair -> Pair
shift p = pair (succ' (fst' p)) (fst' p)

pred' : Nat -> Nat
pred' n = snd' (n  @Pair shift (pair zero zero))

-- Testing

toInt : Nat -> Int
toInt n = n  @Int (\(x : Int) -> x + 1) 0

zero', one, two, three, four : Nat

-- The first numbers
zero' @a s z = z

one @a s z = s z

two @a s z = s (s z)

three @a s z = s (s (s z))

four = succ' three

main : Int
main = toInt $ pred' $ plus one three
-- main = toInt $ exp two $ times four four

-- main : Bool
-- main = isZero $ plus three four
