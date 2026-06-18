module RecData where

data T = C T

-- Not bound to terminate
main : () -> T
main _ = go ()
  where 
    go : () -> T
    go _ = C (main ())
