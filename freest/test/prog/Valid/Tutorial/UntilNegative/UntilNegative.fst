type Repeat = ?Int ; +{Done: Wait, More: Repeat}











-- Repeat until negative
adder : Repeat -> Int
adder (?x ; c) | x < 0  =      c |> select Done |> wait ; 0
adder (?x ; c) | x >= 0 = x + (c |> select More |> adder)




sumTo : Int -> Dual Repeat -> ()
sumTo n c = case send n c of
    &More c -> sumTo (n - 1) c
    &Done c -> close c



_ = forkWith (sumTo 10) |> adder |> print