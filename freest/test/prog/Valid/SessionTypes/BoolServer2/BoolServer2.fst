module BoolServer2 where

type BoolServer : 1C
type BoolServer = &{ And: Skip; ?Bool; ?Bool; !Bool; Skip
                   , Or : Skip; ?Bool; ?Bool; !Bool; Skip
                   , Not: Skip; ?Bool; !Bool; Skip
                   }
                   ; Wait
type BoolClient : 1C
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
              |> receiveAndClose

client2 : BoolClient -> Bool
client2 w = w |> select Not
              |> send True
              |> receiveAndClose 

startClient : (BoolClient -> Bool) -> Bool
startClient client =
  let (w,r) = channel @BoolClient in
  fork (\_ -1-> boolServer r);
  client w

main : ()
main =
  let c1 = startClient client1 in
  let c2 = startClient client2 in
  print (c1 || c2)
