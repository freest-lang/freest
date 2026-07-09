{- |
Module      : SystemFPairs
Description : Pairs in System F
Copyright   : (c) Vasco T. Vasconcelos, 2 jan 2021

Church Encoding _ Pairs
-}

type Pair : *T -> *T -> *T
type Pair a b = forall c -> (a -> b -> c) -> c

fst' : forall a b -> Pair a b -> a
fst' @a @b p = p  @a (\x _ -> x)

snd' : forall a b -> Pair a b -> b
snd' @a @b p = p  @b (\_ y -> y)

pair : forall a b -> a -> b -> Pair a b
pair @a @b x y = \@c z -> z x y

intBoolPair : Int -> Bool -> Pair Int Bool
intBoolPair = pair  @Int @Bool

main : ()
main = print 
     $ snd'  @Int @Char 
     $ fst'  @(Pair Int Char)  @Bool
     $ pair  @(Pair Int Char)  @Bool (pair  @Int @Char 5 'c') False

