
countLines : Int -> InStream -> (Int, InStream)
countLines n inp =
  let (eof, inp) = hIsEOF inp in
  if eof
  then (n, inp)
  else let (_, inp) = hGetLine inp in
       countLines (n + 1) inp

main : ()
main =
  let (n, inp) = stdin |> receive_ |> countLines 0 in
  hCloseIn inp;
  putStrLn $ "Number of lines: " ++ show n
