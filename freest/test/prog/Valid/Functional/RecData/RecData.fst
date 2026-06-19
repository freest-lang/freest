module RecData where

type T : *T
data T = C T

-- Not bound to terminate
f : () -> T
f _ = C (f ())

main : T
main = f ()