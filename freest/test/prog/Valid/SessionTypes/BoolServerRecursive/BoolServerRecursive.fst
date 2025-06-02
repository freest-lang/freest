module BoolServerRecursive where

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
      let c = send (n1 && n2) c in
      boolServer c
    &Or c ->
      let (n1, c) = receive c in
      let (n2, c) = receive c in
      let c = send (n1 || n2) c in
      boolServer c
    &Not c ->
      let (n, c) = receive c in
      -- let c = send c (not n) in
      -- boolServer c,
      (boolServer (send (not n) c))
    &Done c -> wait c

client1 : BoolClient -> Bool
client1 c =
  let (x, c) = 
    select And c
    |> send True
    |> send True
    |> receive in 
  let (y, c) = 
    select Not c
    |> send x 
    |> receive in
  select Done c |> close ;
  y

main : Bool
main =
  let (w, r) = channel @BoolClient in
  let x = fork @() (\(_ : ()) 1-> boolServer r) in
  client1 w
