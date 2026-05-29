{-

Based on the 'Ami and Boe' example from
    'Towards Races in Linear Logic', Wen Kokke, J. Garret Morris, And Philip Waddler

-}

module CakeStore where

type CakeStore : *C
type CakeStore   = *?CakeService

type CakeService : 1C
type CakeService = &{Cake: Close, Disappointment: Close}

runCakeStore : Dual CakeStore -> Bool -> ()
runCakeStore cakeStore gotCake =
    let s = accept cakeStore in
    if gotCake
    then 
        s |> select Cake |> wait;
        runCakeStore cakeStore False
    else 
        s |> select Disappointment |> wait

storeClient : String -> CakeStore -> ()
storeClient name cakeStore =
  case receive_ cakeStore of
    &Cake           c -> putStrLn (name ++ " got cake!"         ); close c
    &Disappointment c -> putStrLn (name ++ " got disappointment"); close c

main : ()
main =
    let (c, s) = channel @CakeStore in
    fork (\(_ : ()) -1-> storeClient "Ami" c);
    fork (\(_ : ()) -1-> storeClient "Boe" c);
    runCakeStore s True
