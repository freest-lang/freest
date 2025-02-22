module ChainOfChannelOps where

type T = +{More: !Int;T, Stop: Close}

g : Dual T -> Int
g r =
  case r of
   	&More r ->
      let (v, r) = receive r in
      v + g r
    &Stop r -> wait r; 0


main : Int
main =
  let (w, r) = channel @T in
  fork @() (\_:()1-> select More w |> send 5 |> select More |> send 2 |> select Stop |> close);
  g r