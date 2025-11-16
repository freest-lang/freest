module ChannelTypeMismatchHO where

main : Int
main =
  let (o, i) = channel @(!)
      (n, i) = close (send 0 o) ; receive i
  in wait i; n