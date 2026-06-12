module LinConsumedInGuard where

f : (Int -1-> Bool) -> Int
f g | g 5       = 0
    | otherwise = if g 6 then 1 else 2
