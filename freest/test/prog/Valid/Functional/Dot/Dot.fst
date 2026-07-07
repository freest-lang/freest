dot : forall a b c -> (b -> c) -> (a -> b) -> a -> c
dot @a @b @c f g x = f (g x)

double : Int -> Int
double x = 2 * x

isZero : Int -> Bool
isZero x = x == 0

main : ()
main = print (dot isZero double 7)
