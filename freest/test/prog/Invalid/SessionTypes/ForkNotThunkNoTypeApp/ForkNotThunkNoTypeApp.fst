module ForkNotThunkNoTypeApp where

main : Int
main =
  let (w, r) = channel @(!Int; Close) in
  fork (w |> send 5 |> close);
  receiveAndWait @Int r

