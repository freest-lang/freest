-- This is clearly a buggy program.
-- It may end with '5' and 'close' in the buffer.
-- To get it right fork the sending side instead.

apply : (?Int;Wait -> (Int, Wait)) -> ?Int; Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    fork (\_ -1-> r |> apply receive |> snd |> wait);
    w |> send 5 |> close
