foo : Int -> Close -> ()
foo n c | n > 0     = close c
        | otherwise = ()
