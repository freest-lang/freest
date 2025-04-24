module SendAndClose where

main : Int
main =
  forkWith @(?Int ; Wait) @() (sendAndClose @Int 5)
    |> receiveAndWait @Int
