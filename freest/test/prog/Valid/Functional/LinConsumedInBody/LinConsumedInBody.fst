module LinConsumedInBody where

ok : Bool -> (Int -1-> ()) -> ()
ok b g | b         = g 1
       | otherwise = g 2

main : ()
main = ok True (\x -1-> ())
