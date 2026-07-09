type Code : *T
type Code = Stream -> Stream

type Stream, RStream : 1C
type Stream = +{More: !Int; Stream, Done: Close}
type RStream = +{Repeat: !Int;!Code ; RStream, Done: Close}

sender : RStream -> ()
sender r =
    let code1 = (\(ch : Stream) -> ch |> select More |> send 1) in
    let r = r |> select Repeat |> send 1 |> send code1 in
    let code2 = (\(ch : Stream) -> ch |> select More |> send 2) in
    let r = r |> select Repeat |> send 2 |> send code2 in
    close (select Done r)

genRepeatCode : Int -> Code -> Code
genRepeatCode 0 co = (\(ch : Stream) -> ch)
genRepeatCode n co =
    let x = genRepeatCode (n-1) co in
    (\(ch : Stream) -> co (x ch))

repeater : Dual RStream -> Stream -1-> ()
repeater r s =
    case r of
        &Repeat r ->        
            let (times, r) = receive r in
            let (code, r) = receive r in
            let co = genRepeatCode times code in
            let s = co s in
            repeater r s
        &Done r ->
            wait r ; 
            close (select Done s)

receiver : Dual Stream -> Int
receiver (&Done s) = wait s ; 0
receiver (&More s) = let (i , s) = receive s in i + receiver s

main : ()
main =
    let (s, rp1) = channel @RStream in
    let (rp2, rc) = channel @Stream in
    fork (\_ -1-> sender s) ;
    fork (\_ -1-> repeater rp1 rp2) ;
    let res = receiver rc in
    print(res)