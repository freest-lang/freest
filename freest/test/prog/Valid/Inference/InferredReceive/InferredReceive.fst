module InferredReceive where

-- `a` appears in a `;` (session) and in a tuple result; both inferred.
recvInt : forall a -> (?Int ; a) -> (Int, a)
recvInt @a c = receive c

main : ()
main =
    let (c, s) = channel @(!Int ; Close) in
    fork (\_ -1-> close (send 17 c));
    let (n, s) = recvInt @Wait s in
    wait s;
    print n
