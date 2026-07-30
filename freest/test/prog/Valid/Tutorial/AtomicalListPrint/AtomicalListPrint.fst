printAList : forall a -> [a] -> *?OutStream -1-> ForkJoin -1-> ()
printAList xs c d = printL xs (receive_ c |> hPutStr "[") ; join d ; ()
    where
        printL : forall a -> [a] -> OutStream -1-> ()
        printL []      c = c |> hPutStr "]\n"      |> hCloseOut
        printL [x]     c = c |> hPutStr (show x) |> hPutStr "]\n" |> hCloseOut
        printL (x::xs) c = c |> hPutStr (show x) |> hPutStr "," |> printL xs

downTo : Int -> [Int]
downTo 0 = []
downTo n = n :: downTo (n - 1)

_ = let n = 6
        (w, r) = channel @ForkJoin in
    parallel n (\_ -> printAList (downTo 200) stdout w) ;
    await n r

    -- The verbose version
-- _ = let n = 6
--         (w, r) = channel @*+{Join} in
--     fork (\_ -> printAList (downTo 200) stdout w) ;
--     fork (\_ -> printAList (downTo 200) stdout w) ;
--     fork (\_ -> printAList (downTo 200) stdout w) ;
--     fork (\_ -> printAList (downTo 200) stdout w) ;
--     case r of *&Join -> case r of *&Join -> case r of *&Join -> case r of *&Join -> ()