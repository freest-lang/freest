-- _ =
--   let (j, a) = channel @ForkJoin in
--   fork (\_ -> putChar 'a' ; join j) ;
--   fork (\_ -> putChar 'b' ; join j) ;
--   fork (\_ -> putChar 'c' ; join j) ;
--   fork (\_ -> putChar 'd' ; join j) ;
--   await 4 a
  
-- _ =
--   let (j, a) = channel @ForkJoin in
--   fork (\_ -> putChar 'a' ; putChar 'b' ; join j) ;
--   fork (\_ -> putChar 'c' ; putChar 'd' ; join j) ;
--   await 2 a

put2Chars : Char -> Char -> ()
put2Chars a b = receive_ stdout |> hPutChar a |> hPutChar b |> hCloseOut

-- _ =  let (j, a) = channel @ForkJoin in
--   fork (\_ -> put2Chars 'a' 'b' ; join j) ;
--   fork (\_ -> put2Chars 'c' 'd' ; join j) ;
--   await 2 a

-- _ = stdout |> receive_ |> hPutStr "hi" |> hCloseOut

-- _ =
--     let (str, instream) = stdin |> receive_ |> hGetLine in
--     hCloseIn instream ; 
--     print str

_ = print $ getLine ()
