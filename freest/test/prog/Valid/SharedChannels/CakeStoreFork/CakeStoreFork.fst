{-

Based on the 'Ami and Boe' example from
    'Towards Races in Linear Logic', Wen Kokke, J. Garret Morris, And Philip Wadler

-}

module CakeStoreFork where

type CakeStore : *C
type CakeStore   = *?CakeService

type CakeService : 1C
type CakeService = &{Cake: Close, Disappointment: Close}

type Fork, Join : *C
type Fork = *+{Over}
type Join = Dual Fork

waitFor : Int -> Join -> ()
waitFor n join =
  if n == 0
  then ()
  else case join of &Over _ -> waitFor (n - 1) join

handleClient : Bool -> Fork -> Dual CakeService -> ()
handleClient gotCake f s =
  -- Whishful :
  -- s |> (if gotCake then select Cake else select Disappointment) |> wait
  (if gotCake then select Cake s else select Disappointment s) |> wait ; 
  select Over f; ()

runCakeStore : Bool -> Int -> Int -> Dual CakeStore -> (Fork, Join) -> ()
runCakeStore gotCake k n cakeStore fj =
  if k == 0 then waitFor n (snd fj)
  else
    let s = accept cakeStore in
    fork #1 (\(_ : ()) -1-> handleClient gotCake (fst fj) s);
    runCakeStore False (k - 1) n cakeStore fj

storeClient : String -> CakeStore -> ()
storeClient name cakeStore =
  case receive_ cakeStore of
    &Cake           c -> putStrLn ((++) #* name " got cake!"         ); close c
    &Disappointment c -> putStrLn ((++) #* name " got disappointment"); close c

main : ()
main =
  let (c, s) = channel @CakeStore in
  fork #1 (\(_ : ()) -1-> storeClient "Ami" c);
  fork #1 (\(_ : ()) -1-> storeClient "Boe" c);
  fork #1 (\(_ : ()) -1-> storeClient "Cai" c);
  runCakeStore True 3 3 s (channel @Fork)
