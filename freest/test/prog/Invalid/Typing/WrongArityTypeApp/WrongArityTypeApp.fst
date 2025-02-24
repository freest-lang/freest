module WrongArityTypeApp where

fst' : forall a:*T b:*T. (a, b) -> a
fst' @a @b p = let (x, _) = p in x

main: Int
main = fst' @Bool (True, 7)
