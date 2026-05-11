module PolySUSL where

id' : forall (a : 1T) -> a -> a
id' @a x = x

main : Int
main =
  let (w, r) = id' (channel @(!Int;Close)) in
  let x = fork #1 (\(_ : ()) -1-> send 5 w |> close) in
  receiveAndWait r 
