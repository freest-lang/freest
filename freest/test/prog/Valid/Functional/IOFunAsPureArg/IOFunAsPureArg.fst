module IOFunAsPureArg where

f : ?Int;Wait -> Int
f c = let (x, c) = receive c in wait c; x

sender : !Int;Close -> Int 1-> ()
sender c i = send (i * 2) c |> close

main : Bool
main =
  let (s, r) = channel @(!Int;Close) in
  fork @() (\_:()1-> sender s 5);
  (div (f r) 2) == 5
