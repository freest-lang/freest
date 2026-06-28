module InferredDeclSession where

-- Declaration-kind inference for a session type with no signature: the body
-- ends in `Close`, so the chan predicate infers `Stream : 1C` (a linear
-- channel), letting it be used directly with `channel`/`fork`.
type Stream = !Int ; !Int ; Close

main : ()
main =
    let (c, s) = channel @Stream in
    fork (\_ -1-> close (send 2 (send 1 c)));
    let (x, s) = receive s in
    let (y, s) = receive s in
    wait s;
    print (x + y)
