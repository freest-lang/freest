module Math1 where

type MathServer, MathClient : 1S
type MathServer = &{Negate: ?Int;!Int, Add: ?Int;?Int;!Int};Wait
type MathClient = Dual MathServer

mathServer : MathServer -> ()
mathServer c =
  case c of
    &Negate c ->
      let (n, c) = receive @Int @(!Int;Wait) c in
      wait (send @Int (-n) @Wait c)
    &Add c ->
      let (n1, c) = receive @Int @(?Int;!Int;Wait) c in
      let (n2, c) = receive @Int @(!Int;Wait) c in
      wait (send @Int (n1 + n2) @Wait c)

main : Int
main =
  let (w,r) = channel @MathClient in
  let _ = fork @() (\(_:()) 1-> mathServer r) in
  receiveAndClose @Int (send @Int 18 @(?Int;Close) (send @Int 5 @(!Int;?Int;Close) (select Add w)))
