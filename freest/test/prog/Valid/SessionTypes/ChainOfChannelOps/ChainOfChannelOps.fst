module ChainOfChannelOps where

type T : 1C
type T = +{More: !Int;T, Stop: Close}

g : Dual T -> Int
g r =
  case r of
   	&More r ->
      let (v, r) = receive @Int @(Dual T) r in
      v + g r
    &Stop r -> let _ = wait r in 0


main : Int
main =
  let (w, r) = channel @T in
  let _ = fork @() (\(_:()) 1-> close (select Stop (send @Int 2 @T (select More (send @Int 5 @T (select More w)))))) in
  g r