-- Writes a file with `openWriteFile`, extends it with `openAppendFile`, and
-- reads it back with `openReadFile`. Writing again with `openWriteFile`
-- discards the previous content.

path : FilePath
path = "/tmp/freest-test-open-write-file.txt"

write : (FilePath -> Maybe' OutStream) -> String -> ()
write open s = case open path of
  Just' out -> out |> hPutStr s |> hCloseOut
  Nothing'  -> putStrLn "cannot open for writing"

contents : () -> String
contents _ = case openReadFile path of
  Just' inp ->
    let (s, inp) = hGetContent inp in
    hCloseIn inp;
    s
  Nothing' -> "cannot open for reading\n"

main : ()
main =
  write openWriteFile "one\n";
  write openAppendFile "two\n";
  putStr (contents ());
  write openWriteFile "three\n";
  putStr (contents ())
