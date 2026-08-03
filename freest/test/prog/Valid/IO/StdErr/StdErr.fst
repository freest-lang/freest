-- Writing on stderr must not show up on stdout, which is all this test can
-- check: the harness compares the program's stdout against the expectation.
_ = hPutStrLn_ "on stderr" stderr ;
    putStrLn "on stdout" ;
    hPutStr_ "on stderr again\n" stderr
