{-
Based on the 'Ami and Boe' example from
'Towards Races in Linear Logic', Wen Kokke, J. Garret Morris,
and Philip Waddler. LMCS 2020.
-}

-- A linear channel, running a session between a client and the store
type CakeService = &{Cake: Close, Disappointment: Close}






-- A shared channel, shared by all clients (and the store)
type CakeStore   = *?CakeService




runCakeStore : Bool -> Dual CakeStore -> ()
runCakeStore False cakeStore  =
    accept cakeStore |> select Disappointment |> wait
runCakeStore True cakeStore  =
    accept cakeStore |> select Cake |> wait ;
    runCakeStore False cakeStore 





storeClient : String -> CakeStore -> ()
storeClient name cakeStore = client (receive_ cakeStore)
    where
        client : CakeService -> ()
        client (&Cake c)           = putStrLn (name ++ " got cake!"         ) ; close c
        client (&Disappointment c) = putStrLn (name ++ " got disappointment") ; close c




_ = let (c, s) = channel @CakeStore in
    fork (\_ -1-> storeClient "Ami" c);
    fork (\_ -1-> storeClient "Boe" c);
    runCakeStore True s
