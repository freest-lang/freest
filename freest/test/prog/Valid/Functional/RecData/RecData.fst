module RecData where

data T = C T

-- Not bound to terminate
f : () -> T
f _ = C (f ())

main : T
main = f ()