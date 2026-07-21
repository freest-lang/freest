echoLines : Int -> InStream -> InStream
echoLines n inp | n <= 0    = inp
echoLines n inp | otherwise =
    let (line, inp) = hGetLine inp in
       putStrLn line;
       echoLines (n - 1) inp

_ =
  receive_ stdin |> echoLines 3 |> hCloseIn