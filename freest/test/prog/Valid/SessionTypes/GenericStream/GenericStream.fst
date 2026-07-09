type GStream = +{ More: !type (a:*T). !a ; GStream, Done: Close }

sender : GStream -> ()
sender ch = ch
    |> select More |> sendType @Int |> send 1
    |> select More |> sendType @Bool |> send True
    |> select More |> sendType @Char |> send 'a'
    |> select More |> sendType @Int |> send 2
    |> select Done |> close

countReceived : Dual GStream -> Int
countReceived (&Done Wait) = 0
countReceived (&More (?type a . ?i ; ch)) = 1 + countReceived ch

main = ()
main =
    let (s, r) = channel @GStream in
    fork (\_ -1-> sender s) ;
    print(countReceived r)