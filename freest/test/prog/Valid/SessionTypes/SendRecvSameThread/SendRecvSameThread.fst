module SendRecvSameThread where

main : Int
main =
  let (w, r) = channel @(!Int;Close) in
  w |> send 5 |> close;
  let (x, r) = receive r in
  wait r;
  x
