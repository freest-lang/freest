addOne : Int -> Int
addOne = (+ 1)

main : ()
main = print $ addOne 4 + (* 3) 10 + (if (< 10) 3 then 100 else 0)
