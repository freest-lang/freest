module Math where

type MathServer = &{Negate: ?Int;!Int, Add: ?Int;?Int;!Int} ; Wait

mathServer : MathServer-> ()
mathServer c =
  case c of
    &Negate c ->
      let (n, c) = receive c in
      c |> send (-n) |> wait
    &Add c ->
      let (n1, c) = receive c in
      let (n2, c) = receive c in
      c |> send (n1 + n2) |> wait

main : Int
main =
  let (r,w) = channel @MathServer in
  let _ = fork (\_:()1-> mathServer r) in
  w |> select Negate |> send 5 |> receiveAndClose @Int
