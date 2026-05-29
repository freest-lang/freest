module PartialReceive where

apply : (?Int;Wait -> (Int, Wait)) -> ?Int; Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    fork (\(_ : ()) -1-> r |> apply (receive @Int @Wait {- CANNOT INFER -}) |> snd |> wait);
    w |> send 5 |> close