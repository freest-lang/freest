module Math where

type MathServer : 1C
type MathServer = &{Negate: ?Int;!Int, Add: ?Int;?Int;!Int} ; Wait

mathServer : MathServer-> ()
mathServer c =
  case c of
    &Negate c ->
      let (n, c) = receive @Int @(!Int; Wait) c in
      wait (send @Int (-n) @Wait c)
    &Add c ->
      let (n1, c) = receive @Int @(?Int;!Int;Wait) c in
      let (n2, c) = receive @Int @(!Int;Wait) c in
      wait (send @Int (n1 + n2) @Wait c)

main : Int
main =
  let (r,w) = channel @MathServer in
  let _ = fork @() (\(_:()) 1-> mathServer r) in
  receiveAndClose @Int (send @Int 5 @(?Int;Close) (select Negate w))
