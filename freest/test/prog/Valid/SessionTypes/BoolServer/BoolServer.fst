module BoolServer where

type BoolServer, BoolClient : 1C
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
      c3 |> send (n1 && n2) |> wait
    &Or c1 ->
      let (n1, c2) = receive c1 in
      let (n2, c3) = receive c2 in
      c3 |> send (n1 || n2) |> wait
    &Not c1 ->
      let (n1, c2) = receive c1 in
      c2 |> send (not n1)   |> wait

client1 : BoolClient -> Bool
client1 w = w |> select And
              |> send True  
              |> send False
              |> receiveAndClose @Bool 

startClient : (BoolClient -> Bool) -> Bool
startClient client =
  let (w,r) = channel @BoolClient in
  fork @() (\(_ : ()) 1-> boolServer r);
  client w

main : Bool
main = startClient client1

-- remove skips from the end
-- Type check : environment checks only the linear part (filter)
