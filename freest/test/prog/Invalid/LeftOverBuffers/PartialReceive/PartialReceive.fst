-- Ends with '5' and 'close' in a buffer: the main thread sends and closes,
-- and terminates before the forked thread receives. The fixed version, in
-- Valid/SessionTypes/PartialReceive, forks the sending side instead.

apply : (?Int;Wait -> (Int, Wait)) -> ?Int; Wait -> (Int, Wait)
apply f = f

main : ()
main =
    let (r, w) = channel @(?Int;Wait) in
    fork (\_ -1-> r |> apply receive |> snd |> wait);
    w |> send 5 |> close
