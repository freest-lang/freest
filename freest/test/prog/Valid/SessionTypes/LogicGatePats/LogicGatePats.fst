type BStream : 1C
type BStream = +{More: !Bool; BStream, Done: Close}

type BinOp : *T
type BinOp = Bool -> Bool -> Bool

consumeAndEnd : Dual BStream -> ()
consumeAndEnd (&Done Wait) = ()
consumeAndEnd (&More (?b ; r)) = consumeAndEnd r

logicGate : BinOp -> Dual BStream -> Dual BStream -1-> BStream -1-> ()
logicGate binOp (&More (?b1 ; r1)) (&More (?b2 ; r2)) s = 
    let s = s |> select More |> send (binOp b1 b2) in
    logicGate binOp r1 r2 s
logicGate binOp (&Done Wait)       (&Done Wait)       s = s |> select Done |> close
logicGate _     (&Done Wait)       (&More (?_ ; r2))  s =
    consumeAndEnd r2 ; 
    s |> select Done |> close
logicGate _     (&More (?_ ; r1))  (&Done Wait)       s =
    consumeAndEnd r1 ; 
    s |> select Done |> close

sender1 : BStream -> ()
sender1 ch = ch
    |> select More |> send True
    |> select More |> send True
    |> select More |> send False
    |> select More |> send False
    |> select Done |> close

sender2 : BStream -> ()
sender2 ch = ch
    |> select More |> send True
    |> select More |> send False
    |> select More |> send True
    |> select More |> send False
    |> select Done |> close

senderShort : BStream -> ()
senderShort ch = ch
    |> select More |> send True
    |> select More |> send False
    |> select Done |> close

receiver : Dual BStream -> ()
receiver (&Done Wait) = ()
receiver (&More (?b ; r)) = 
    print b ;
    receiver r

main : ()
main =
    let (s1, r1) = channel @BStream in
    let (s2, r2) = channel @BStream in
    let (s, r) = channel @BStream in
    fork (\_ -1-> sender1 s1) ;
    -- fork (\_ -1-> sender2 s2) ;
    fork (\_ -1-> senderShort s2) ;
    fork (\_ -1-> logicGate (&&) r1 r2 s) ;
    receiver r