module RecData where

type T : *T
data T = C T

-- Not bound to terminate
main : T
main = go ()
  where 
    go : () -> T
    go _ = C (main ())
