module PartialReceive where

apply : (?Int;Wait -> (Int, Wait)) -> ?Int;Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    fork  @() (\_:()1-> wait (snd @Int @Wait (apply (receive  @Int @Wait) r))) ;
    send 5 w |> close
