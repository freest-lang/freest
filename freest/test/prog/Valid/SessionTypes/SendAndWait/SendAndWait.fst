module SendAndWait where

main : ()
main =  
  forkWith @(!Int ; Wait) @Int (receiveAndClose @Int) 
    |> sendAndWait @Int 5
