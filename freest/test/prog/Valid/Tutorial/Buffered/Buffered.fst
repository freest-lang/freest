type SendIntInt = !Int ; !Int ; Close

writeInts : SendIntInt -> ()
writeInts c = c |> send 1 |> send 2 |> close

readInts : Dual SendIntInt -> Int
readInts (?x ; ?y ; Wait) = x + y

_ = let (x, y) = channel @SendIntInt
    in writeInts x ;
       print $ readInts y

_ = forkWith writeInts |> readInts |> print

{- freest: thread blocked indefinitely in an MVar operation
type SendIntInt = !Int ; !Int ; Wait

writeInts : SendIntInt -> ()
writeInts c = c |> send 1 |> send 2 |> wait

readInts : Dual SendIntInt -> Int
readInts (?x ; ?y ; c) = close c ;x + y

_ = let (x, y) = channel @SendIntInt
    in writeInts x ;
       print $ readInts y

_ = forkWith writeInts |> readInts |> print
-}
