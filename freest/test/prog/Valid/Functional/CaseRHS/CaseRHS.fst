module CaseRHS where

even : Int -> Bool
even 0 = True
even n | even (n - 1) = False
       | otherwise    = True

main : ()
main = case 0 of
  0 -> ()
    where x = 1
  n | even n -> ()
    | otherwise -> ()
