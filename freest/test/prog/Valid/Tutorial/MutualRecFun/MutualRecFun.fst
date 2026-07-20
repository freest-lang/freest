-- Natural numbers domain
mutual
  even : Int -> Bool
  even 0 = True
  even n = odd (n - 1)
  odd : Int -> Bool
  odd n = not (even n)

-- mutual
--   even : Int -> Bool
--   even 0 = True
--   even n = odd (n - 1)
--   odd : Int -> Bool
--   odd 0 = False
--   odd n = even (n - 1)

-- Integer domain
mutual 
  even' : Int -> Bool
  even' 0 = True
  even' n
    | n > 0     = odd' (n - 1)
    | otherwise = odd' (n + 1)
  odd' : Int -> Bool
  odd' 0 = False
  odd' n
    | n > 0     = even' (n - 1)
    | otherwise = even' (n + 1)

_ = print (even' 84 && even 84)

_ = print (odd' 84)

improvedDivision : Int -> Int -> (Int, Int)
improvedDivision n div =
    let quotient = n / div
        remainder = mod n div
    in (quotient, remainder)
