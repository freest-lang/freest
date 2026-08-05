type Chan : 1C
type Chan = !type a. (!a ; !(a -> Int) ; Close)

sendInt : Chan -> !Int ; !(Int -> Int) ; Close
sendInt = sendType @Int

recvType : Dual Chan -> (exists (a : *T), (?a ; ?(a -> Int) ; Wait))
recvType = receiveType

server : Dual Chan -> Int
server s =
  let (@a, s) = recvType s in
  let (x, s) = receive s in
  let (f, s) = receive s in
  wait s;
  f x

main : ()
main =
  let (c, s) = channel @Chan in
  fork (\_ -1-> c |> sendInt |> send 5 |> send (\(x : Int) -> x + 1) |> close);
  print @Int (server s)
