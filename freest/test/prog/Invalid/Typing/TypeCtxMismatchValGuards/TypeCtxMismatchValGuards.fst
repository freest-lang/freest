module TypeCtxMismatchValGuards where

foo : ()
foo =
  let (o, i) = channel @Close
      n = 1
      x | n > 0 = close o; wait i
        | otherwise = ()
  in return x 