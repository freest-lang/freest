module BoolServer2 where

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
      let (n1, c2) = receive @Bool @(?Bool;!Bool;Wait) c1 in
      let (n2, c3) = receive @Bool @(!Bool;Wait) c2 in
      wait (send @Bool (n1 && n2) @Wait c3)
    &Or c1 ->
      let (n1, c2) = receive @Bool @(?Bool;!Bool;Wait) c1 in
      let (n2, c3) = receive @Bool @(!Bool;Wait) c2 in
      wait (send @Bool (n1 || n2) @Wait c3)
    &Not c1 ->
      let (n1, c2) = receive @Bool @(!Bool;Wait) c1 in
      wait (send @Bool (not n1) @Wait c2)

client1 : BoolClient -> Bool
client1 w = receiveAndClose @Bool (send @Bool False @(?Bool;Close) (send @Bool True @(!Bool;?Bool;Close) (select And w)))

client2 : BoolClient -> Bool
client2 w = receiveAndClose @Bool (send @Bool True @(?Bool;Close) (select Not w))

startClient : (BoolClient -> Bool) -> Bool
startClient client =
  let (w,r) = channel @BoolClient in
  (;) @() @Bool
    (fork @() (\(_ : ()) 1-> boolServer r))
    (client w)

main : Bool
main =
  let c1 = startClient client1 in
  let c2 = startClient client2 in
  c1 || c2

-- remove skips from the end
-- Type check : environment checks only the linear part (filter)
