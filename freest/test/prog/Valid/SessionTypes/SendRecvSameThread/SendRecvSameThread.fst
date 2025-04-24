module SendRecvSameThread where

main : Int
main =
  let (w, r) = channel @(!Int;Close) in
  let w    = send 5 w |> close in
  let (x, r) = receive r in
  wait r;
  x
