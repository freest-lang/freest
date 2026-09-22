type Stream : 1C
type Stream = +{ More: !Int ; Stream, Done: Close }

-- dropS : Int -> Dual Stream -> Dual Stream
-- dropS n (&Done Wait) = ??
-- dropS n (&More ch) = let (_, ch) = receive ch in dropS (n-1) ch
-- dropS n (&More (?_ ; ch)) = dropS (n-1) ch
-- the issue with dropS is that the function must return a channel of type Stream but no actions remain on the channel

-- takeS : Int -> DualStream -> Dual Stream
-- the issue with takeS is that we can't isolate the first n actions while discarding the remaining

-- to get around this, we can instead opt for a two channel architecture, where we replicate the actions to pass to another channel

dropS : Int -> Dual Stream -1-> Stream -1-> ()
-- dropS n (&Done Wait) outCh = close (select Done outCh)
dropS n (&Done inCh) outCh = wait inCh ; close (select Done outCh)
-- dropS n (&More (?i ; inCh)) outCh = 
--     let outCh = if n == 0 then outCh |> select More |> send i else outCh in
--     dropS (n-1) inCh outCh
dropS n (&More inCh) outCh = 
    let (i, inCh) = receive inCh in
    let outCh = if n == 0 then outCh |> select More |> send i else outCh in
    dropS (n-1) inCh outCh

takeS : Int -> Dual Stream -1-> Stream -1-> ()
takeS n (&Done inCh) outCh = wait inCh ; close (select Done outCh)
takeS n (&More inCh) outCh = 
    let (i, inCh) = receive inCh in
    let outCh = if n > 0 then outCh |> select More |> send i else outCh in
    takeS (n-1) inCh outCh 

receiver : Dual Stream -> ()
receiver (&Done Wait) = ()
receiver (&More (?n ; ch)) = print n ; receiver ch

main : ()
main =
  let (s1, r1) = channel @Stream in
  let (s2, r2) = channel @Stream in
  fork (\_ -1-> s1 |> select More |> send 1
                     |> select More |> send 2
                     |> select More |> send 3
                     |> select Done |> close) ;
  fork (\_ -1-> takeS 3 r1 s2) ;
  receiver r2


-- consumeAll : forall a -> Dual Stream ; a -> a
-- consumeAll @a (&Done ch) = ch
-- consumeAll @a (&More ch) = let (_, ch) = receive ch in consumeAll ch

-- dropS : forall a -> Int -> Dual Stream ; a -> Stream ; a -> ()
-- dropS 0 inCh outCh = 
-- dropS n (&Done ch) = select 
-- dropS n (&More ch) = let (_, ch) = receive ch in dropS (n-1) ch