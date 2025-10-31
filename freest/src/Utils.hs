{- |
Module      :  Utils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Miscellaneous utility functions.
-}
module Utils 
  ( internalError
  , ordinal
  , strip
  , lstrip
  , rstrip
  , rpad
  )
where

-- | Throw an 'error' with standard formatting.
internalError :: String -> a
internalError s = error $ "(Internal error) "++s

-- | The ordinal 'String' of an 'Integral'.
ordinal :: (Integral a, Show a) => a -> String
ordinal i = show i ++ suffix
  where suffix | i' > 10 && i' < 20 = "th"
               | otherwise = suffix' (i' `mod` 10)
        suffix' = \case 1->"st"; 2->"nd"; 3->"rd"; _->"th"
        i' = abs i 

-- | From MissingH. Removes any whitespace characters that are present at the
-- start or end of a string.
strip :: String -> String
strip = lstrip . rstrip

-- | From MissingH. Same as 'strip', but applies only to the left side of the
-- string.
lstrip :: String -> String
lstrip = \case 
  []                 -> []
  s@(x:xs) 
    | elem x " \t\r\n" -> lstrip xs
    | otherwise      -> s

-- | From MissingH. Same as 'strip', but applies only to the right side of the
-- string.
rstrip :: String -> String
rstrip = reverse . lstrip . reverse

rpad n c s = s ++ replicate (n - length s) c

lpad n c s = replicate (n - length s) c ++ s