-- Each opening operation yields `Nothing'` when the file cannot be opened:
-- a file that does not exist for reading, and a file in a directory that
-- does not exist for writing and appending.

missingDir : FilePath
missingDir = "/tmp/freest-test-no-such-directory/file.txt"

report : forall (a : 1C) -> String -> (a -> ()) -> Maybe' a -> ()
report name _   Nothing'  = putStrLn (name ++ ": Nothing'")
report name use (Just' c) = use c; putStrLn (name ++ ": Just'")

main : ()
main =
  report "openReadFile"   hCloseIn  (openReadFile "/tmp/freest-test-no-such-file.txt");
  report "openWriteFile"  hCloseOut (openWriteFile missingDir);
  report "openAppendFile" hCloseOut (openAppendFile missingDir)
