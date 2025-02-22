module Math1 where

type MathServer = &{Negate: ?Int;!Int, Add: ?Int;?Int;!Int};Wait
type MathClient = Dual MathServer

mathServer : MathServer -> ()
mathServer c =
  case c of
    &Negate c ->
      let (n, c) = receive c in
      send (-n) c
      |> wait
    &Add c ->
      let (n1, c) = receive c in
      let (n2, c) = receive c in
      send (n1 + n2) c
      |> wait

main : Int
main =
  let (w,r) = channel @MathClient in
  fork @() (\_:()1-> mathServer r);
  w |> select Add 
    |> send 5 
    |> send 18
    |> receiveAndClose @Int
