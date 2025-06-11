module BoolServer3 where

type BoolServer : 1S
type BoolServer = &{ And: Skip; ?Bool; ?Bool; !Bool; Skip
                   , Or : Skip; ?Bool; ?Bool; !Bool; Skip
                   , Not: Skip; ?Bool; !Bool; Skip
                   }
                   ; Wait
type BoolClient : 1S
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

client2 : BoolClient -> Bool
client2 w = w |> select Not
              |> send True
              |> receiveAndClose @Bool

startClient : (BoolClient -> Bool) -> Bool
startClient client =
  let (w,r) = channel @BoolClient in
  fork (\(_ : ()) 1-> boolServer r);
  client w

s1 : Bool
s1 =
  let c1 = startClient client1 in
  let c2 = startClient client2 in
  c1 || c2

main : Bool
main = s1


-- remove skips from the end
-- Type check : environment checks only the linear part (filter)
