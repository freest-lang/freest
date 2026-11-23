-- Opens a file in this folder with `openReadFile` and prints its lines,
-- numbered, reading one line at a time until the end of the file.

numberLines : Int -> InStream -> InStream
numberLines n inp =
  let (eof, inp) = hIsEOF inp in
  if eof
  then inp
  else
    let (line, inp) = hGetLine inp in
    putStrLn (show n ++ ": " ++ line);
    numberLines (n + 1) inp

main : ()
main = case openReadFile "test/prog/Valid/IO/OpenReadFile/lines.txt" of
  Just' inp -> inp |> numberLines 1 |> hCloseIn
  Nothing'  -> putStrLn "cannot open lines.txt"
