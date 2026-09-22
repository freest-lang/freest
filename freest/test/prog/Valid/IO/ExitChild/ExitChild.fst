-- an exit in a forked thread ends that thread alone
_ = fork (\_ -1-> exitWith @() 7)
_ = putStrLn "main carried on"
