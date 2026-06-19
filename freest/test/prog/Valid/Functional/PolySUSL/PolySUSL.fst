module PolySUSL where

id' : forall (a : 1T) -> a -> a
id' @a x = x

main : ()
main =
  let (w, r) = id' (channel @(!Int;Close)) in
  let x = fork (\(_ : ()) -1-> send 5 w |> close) in
  print (receiveAndWait r)
