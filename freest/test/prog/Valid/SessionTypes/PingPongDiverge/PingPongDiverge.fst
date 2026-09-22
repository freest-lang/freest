type Ping, Pong : 1C
type Ping = !Int; Pong
type Pong = ?Int; Ping


mutual
  ping : Int -> Ping -> Void @*T
  ping n c = c |> send n |> pong

  pong : Pong -> Void @*T
  pong c =
    let (n, c) = receive c in
    print n;
    ping (n + 1) c

main : Void @*T
main = forkWith (\(c : Ping) -1-> ping 0 c) |> pong
