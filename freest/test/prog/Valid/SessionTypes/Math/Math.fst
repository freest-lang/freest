module Math where

type MathServer : 1C
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

main : ()
main =
  let (r,w) = channel @MathServer in
  fork (\(_ : ()) -1-> mathServer r);
  w |> select Negate |> send 5 |> receiveAndClose |> print
