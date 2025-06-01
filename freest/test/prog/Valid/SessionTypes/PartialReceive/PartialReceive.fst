module PartialReceive where

apply : (?Int;Wait -> (Int, Wait)) -> ?Int;Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    let _ = fork  @() (\(_:())1-> wait (snd @Int @Wait (apply (receive  @Int @Wait) r))) in
    close (send @Int 5 @Close w)
