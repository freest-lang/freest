module SendRecvSameThread where

main : Int
main =
  let (w, r) = channel @(!Int;Close) in
  let _      = close (send @Int 5 @Close w) in
  let (x, r) = receive @Int @Wait r in
  let _      = wait r in
  x
