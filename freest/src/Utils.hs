module Utils 
  ( internalError
  , maybeLeft
  , ordinal
  )
where

internalError :: String -> a
internalError s = error $ "(Internal error) "++s

maybeLeft :: Either a b -> Maybe a
maybeLeft = either Just (const Nothing)

ordinal :: (Integral a, Show a) => a -> String
ordinal i = show i ++ suffix
  where suffix | i' > 10 && i' < 20 = "th"
               | otherwise = suffix' (i' `mod` 10)
        suffix' = \case 1->"st"; 2->"nd"; 3->"rd"; _->"th"
        i' = abs i 