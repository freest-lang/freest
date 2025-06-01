module BoolServer1 where

type BoolClient, BoolServer : 1S

type BoolServer = &{ And: ?Bool; ?Bool; !Bool; Skip
                   , Or : ?Bool; ?Bool; !Bool; Skip
                   , Not: ?Bool; !Bool; Skip
                   }
                   ; Wait
type BoolClient = Dual BoolServer

boolServer : BoolServer -> ()
boolServer c =
  case c of
    &And c1 ->
      let (n1, c2) = receive @Bool @(?Bool; !Bool; Wait) c1 in
      let (n2, c3) = receive @Bool @(!Bool; Wait) c2 in
      wait (send @Bool (n1 && n2) @Wait c3)
    &Or c1 ->
      let (n1, c2) = receive @Bool @(?Bool; !Bool; Wait) c1 in
      let (n2, c3) = receive @Bool @(!Bool; Wait) c2 in
      wait (send @Bool (n1 || n2) @Wait c3)
    &Not c1 ->
      let (n1, c2) = receive @Bool @(!Bool; Wait) c1 in
      wait (send @Bool (not n1) @Wait c2)

client1 : BoolClient -> Bool
client1 w = 
  receiveAndClose @Bool 
    (send @Bool False @(?Bool;Close) 
      (send @Bool True @(!Bool;?Bool;Close) 
        (select Or w)))


main : Bool
main =
  let (w,r) = channel @BoolClient in
  let x = fork @() (\(_:()) 1-> boolServer r) in
  client1 w

-- remove skips from the end
-- Type check : environment checks only the linear part (filter)
