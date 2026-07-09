{- |
Module      : SystemFBooleans
Description : Examples from TAPL, Chapter 23, Universal Types
Copyright   : (c) Vasco T. Vasconcelos, 31 dec 2020

Church Encoding _ Boolean Values
-}

type Bool' : *T
type Bool' = forall b -> b -> b -> b

true, false : Bool'

true  = \@a -> \t -> \f -> t

false = \@a -> \t -> \f -> f

not' : Bool' -> Bool'
not' = \b -> \@a -> \t -> \f -> b @a f t

-- Abbreviated versions of the above

type Bool'' : *T -> *T
type Bool'' b = b -> b -> b

true', false': forall b -> Bool'' b

true'  @b t _ = t

false' @b _ f = f

not'' : forall b -> Bool'' b -> Bool'' b
not'' @b b = \t f -> b f t

-- Destructor

cond : forall a -> Bool' -> a -> a -> a
cond @a b e1 e2 = b @a e1 e2

-- Boolean ops based on the conditional

not''' : Bool' -> Bool'
not''' b = cond  @Bool' b false true

or', and' : Bool' -> Bool' -> Bool'
or' b1 b2 = cond  @Bool' b1 true b2

and' b1 b2 = cond  @Bool' b1 b2 false

-- Testing

toBool : Bool' -> Bool
toBool b = b  @Bool True False

toBit : Bool' -> Int
toBit b = b  @Int 1 0

ifInt : Bool' -> Int -> Int -> Int
ifInt = cond  @Int

-- main : Int
-- main = ifInt (not' true) 1 2

main : ()
main = print $ toBool $ and' (or' false true) (not' false)
