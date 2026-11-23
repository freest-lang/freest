-- `readFile` raises an error when the file cannot be opened.

main : ()
main = putStr (readFile "/tmp/freest-test-no-such-file.txt")
