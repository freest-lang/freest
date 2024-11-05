module Utils 
  (internalError
  )
where

internalError :: String -> a
internalError s = error $ "(Internal error) "++s
