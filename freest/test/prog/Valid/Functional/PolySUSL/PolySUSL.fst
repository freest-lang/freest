module PolySUSL where

id' : a -> a
id' x = x

main : Int
main =
  let (w, r) = id' @(!Int;Close, ?Int;Wait) (channel @(!Int;Close)) in
  let x = fork @() (\_:()1-> send 5 w |> close) in
  receiveAndWait @Int r 
