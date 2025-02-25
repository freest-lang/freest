{- |
Module      :  Utils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Miscellaneous utility functions.
-}
module Utils 
  ( internalError
  , ordinal
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