module InferredContinuation where

-- The session continuation `a` has its kind omitted on the forall; kind
-- inference infers it (1S) from its use in the `;` composition.
sendInt : forall a -> Int -> (!Int ; a) -> a
sendInt @a x c = send x c

main : ()
main =
    let (c, s) = channel @(!Int ; Close) in
    fork (\_ -1-> close (sendInt @Close 42 c));
    let (n, s) = receive s in
    wait s;
    print n
