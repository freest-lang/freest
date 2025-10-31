module ChannelTypeMismatch where

main : Int
main =
  let (o, i) = channel @(!Int)
      (n, i) = close (send 0 o) ; receive i
  in wait i; n