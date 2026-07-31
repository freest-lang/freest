countLines' : InStream -> (Int, InStream)
countLines' inp =
  let (eof, inp) = hIsEOF inp in
  if eof
  then (0, inp)
  else let (_, inp) = hGetLine inp
           (n, inp) = countLines' inp
        in (n + 1, inp)

-- _ =
--   let (n, inp) = stdin |> receive_ |> countLines' in
--   hCloseIn inp;
--   putStrLn $ "Number of lines: " ++ show n

countLines : Int -> InStream -> (Int, InStream)
countLines n inp =
  let (eof, inp) = hIsEOF inp in
  if eof
  then (n, inp)
  else inp |> hGetLine |> snd |> countLines (n + 1)
        
_ =
  let (n, inp) = stdin |> receive_ |> countLines 0 in
  hCloseIn inp;
  putStrLn $ "Number of lines: " ++ show n

