-- Matching only `Just'` fails at runtime when the file cannot be opened.

main : ()
main = case openReadFile "/tmp/freest-test-no-such-file.txt" of
  Just' c -> hCloseIn c
