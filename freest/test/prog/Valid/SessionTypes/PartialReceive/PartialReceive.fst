-- The sending side is forked; the main thread receives, so that the program
-- ends with every channel buffer empty.

apply : (?Int;Wait -> (Int, Wait)) -> ?Int; Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    fork (\_ -1-> w |> send 5 |> close);
    r |> apply receive |> snd |> wait
