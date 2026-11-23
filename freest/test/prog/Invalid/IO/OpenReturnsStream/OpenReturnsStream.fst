-- Opening a file yields a `Maybe' InStream`, not the stream itself.

main : ()
main =
  let (line, c) = hGetLine (openReadFile "test/prog/Valid/IO/OpenReadFile/lines.txt") in
  hCloseIn c;
  putStrLn line
