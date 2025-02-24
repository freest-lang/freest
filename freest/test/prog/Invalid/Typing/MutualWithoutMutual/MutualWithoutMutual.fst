module MutualWithoutMutual where

even : Int -> Bool
even 0 = True 
even n 
  | n > 0     = odd (n - 1)
  | otherwise = odd (n + 1)

odd : Int -> Bool
odd 0 = False
odd n 
  | n > 0     = even (n - 1)
  | otherwise = even (n + 1)