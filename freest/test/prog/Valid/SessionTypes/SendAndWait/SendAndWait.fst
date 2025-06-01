module SendAndWait where

main : ()
main =  
  sendAndWait @Int 5 (forkWith @(!Int ; Wait) @Int (receiveAndClose @Int))
