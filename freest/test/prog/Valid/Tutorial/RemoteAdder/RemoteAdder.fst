adder : ?Int ; ?Int ; !Int ; Wait -> ()
adder c =
    let (x, c) = receive c
        (y, c) = receive c
    in sendAndWait (x + y) c

onePlusOne : !Int ; !Int ; ?Int ; Close -> Int
onePlusOne c =
    c |> send 1 |> send 1 |> receiveAndClose

_ =
    let x = forkWith adder
    in print $ onePlusOne x
