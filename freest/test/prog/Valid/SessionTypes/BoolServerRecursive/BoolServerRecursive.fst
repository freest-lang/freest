module BoolServerRecursive where

type BoolServer, BoolClient : 1S
type BoolServer = &{ And : ?Bool; ?Bool; !Bool; BoolServer
                   , Or  : ?Bool; ?Bool; !Bool; BoolServer
                   , Not : ?Bool; !Bool; BoolServer
                   , Done: Wait
                   }
type BoolClient = Dual BoolServer

boolServer : BoolServer -> ()
boolServer c =
  case c of
    &And c ->
      let (n1, c) = receive c in
      let (n2, c) = receive c in
      c |> send (n1 && n2) |> boolServer
    &Or c ->
      let (n1, c) = receive c in
      let (n2, c) = receive c in
      c |> send (n1 || n2) |> boolServer
    &Not c ->
      let (n, c) = receive c in
      -- let c = send c (not n) in
      -- boolServer c,
      c |> send (not n)   |> boolServer
    &Done c -> wait c

client1 : BoolClient -> Bool
client1 c =
  let (x, c) = c |> select And
                 |> send True
                 |> send True
                 |> receive in 
  let (y, c) = c |> select Not
                 |> send x 
                 |> receive in
  c |> select Done |> close;
  y

main : Bool
main =
  let (w, r) = channel @BoolClient in
  fork (\(_ : ()) 1-> boolServer r);
  client1 w
