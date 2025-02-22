module BoolServer where

type BoolServer, BoolClient : 1S
type BoolServer = &{ And: Skip; ?Bool; ?Bool; !Bool
                   , Or : Skip; ?Bool; ?Bool; !Bool
                   , Not: Skip; ?Bool; !Bool
                   }
                   ; Wait
type BoolClient = Dual BoolServer

boolServer :  BoolServer -> ()
boolServer c =
  case c of
    &And c1 ->
      let (n1, c2) = receive c1 in
      let (n2, c3) = receive c2 in
      send (n1 && n2) c3 
      |> wait
    &Or c1 ->
      let (n1, c2) = receive c1 in
      let (n2, c3) = receive c2 in
      send (n1 || n2) c3
      |> wait
    &Not c1 ->
      let (n1, c2) = receive c1 in
      send (not n1) c2
      |> wait

client1 : BoolClient -> Bool
client1 w = w |> select And
              |> send True  
              |> send False
              |> receiveAndClose @Bool 

startClient : (BoolClient -> Bool) -> Bool
startClient client =
  let (w,r) = channel @BoolClient in
  let x = fork @() (\_:()1-> boolServer r) in
  client w

main : Bool
main = startClient client1

-- remove skips from the end
-- Type check : environment checks only the linear part (filter)
