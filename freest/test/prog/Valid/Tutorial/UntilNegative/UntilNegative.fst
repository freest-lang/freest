type Repeat = ?Int ; +{Done: Wait, More: Repeat}

-- Repeat until negative
adder : Repeat -> Int
adder (?x ; c) | x <= 0  =      c |> select Done |> wait ; 0
adder (?x ; c)           = x + (c |> select More |> adder)

sendDownFrom : Int -> Dual Repeat -> ()
sendDownFrom n c = case send n c of
    &More c -> sendDownFrom (n - 1) c
    &Done c -> close c

_ = forkWith (sendDownFrom 10) |> adder |> print