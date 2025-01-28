module Utils 
  ( internalError
  , maybeLeft
  )
where

internalError :: String -> a
internalError s = error $ "(Internal error) "++s

maybeLeft :: Either a b -> Maybe a
maybeLeft = either Just (const Nothing)