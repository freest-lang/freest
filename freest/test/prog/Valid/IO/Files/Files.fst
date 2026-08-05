-- a file is reachable only as a session endpoint, and linearity closes it
_ = writeFile "/tmp/freest-test-files.txt" "one\ntwo\n"
_ = appendFile "/tmp/freest-test-files.txt" "three\n"
_ = putStr (readFile "/tmp/freest-test-files.txt")
