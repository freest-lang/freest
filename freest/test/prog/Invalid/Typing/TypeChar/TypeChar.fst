module TypeChar where

type C = Char
type B = Bool

-- the commented line gives an error
-- expecting to see C instead of char on the error message

isC : C -> B
isC c = (ord c) == (ord 'c')
-- isC c = (chr c) == (chr 'c') 

type F = C -> B

-- Expecting C on the error message
-- isC' : F
-- isC' c = (chr c) == (ord 'c')

type F' = B -> C

fog : F' -> F -> C -> C
fog f g x = g (f x)

-- f (g x)
-- f : Bool -> Bool
-- g : Int -> Bool


