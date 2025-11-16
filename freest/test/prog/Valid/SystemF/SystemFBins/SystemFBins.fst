{- |
Module      : SystemFBins
Description : Natural numbers as sequences of zeros and ones.
Copyright   : (c) Vasco T. Vasconcelos

Church Encoding _ Binary natural numbers.

Jean-Yves Girard
The Blind Spot
European Mathematical Society, 2011

"The previous integers are <<Cro-Magnon integer>>, anterior to the Babylonian numeration. A more modern version of integers requires finite sequences of zeros and ones." (page 119)
-}

module SystemFBins where

type Bin : *T
type Bin = forall (a : *T) . a -> (a -> a) -> (a -> a) -> a

zero, zero', one, two, three, four, fifteen : Bin

zero    @a z s0 s1 = z                         -- .

zero'   @a z s0 s1 = z |> s0                   -- .0

one     @a z s0 s1 = z |> s1                   -- .1

two     @a z s0 s1 = z |> s1 |> s0             -- .10

three   @a z s0 s1 = z |> s1 |> s1             -- .11

four    @a z s0 s1 = z |> s1 |> s0 |> s0       -- .100

fifteen @a z s0 s1 = z |> s1 |> s1 |> s1 |> s1 -- .11111

isZero : Bin -> Bool
isZero n = n @Bool True (\(_ : Bool) -> False) (\(_ : Bool) -> False)

toInt : Bin -> Int
toInt n = n @Int 0 (\(x : Int) -> 2 * x) (\(x : Int) -> 2 * x + 1)

-- succ' : Bin -> Bin
-- succ' n = \@(a : *T) -> (one @a) (\(s0 : a -> a) -> s0 n @a) (\(s1 : a->a) -> s1 n@a)

-- succ' : Bin -> Bin
-- succ' n = n @Bin
--           one
--           (\(z : Bin) (s0 : Bin->Bin) (s1 : Bin->Bin) -> s0 n)
--           (\(z : Bin) (s0 : Bin->Bin) (s1 : Bin->Bin) -> s1 n)

main : Bool
main = isZero fifteen
-- main = toInt fifteen

-- TO BE CONTINUED
