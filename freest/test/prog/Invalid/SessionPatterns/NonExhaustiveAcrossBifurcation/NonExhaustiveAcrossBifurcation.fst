type Bifurcation = &{ A: ?Bool ; &{B: Wait, C: Wait}}

choice2B : &{B: Wait, C: Wait} -> ()
choice2B (&B Wait) = ()

choice2C : &{B: Wait, C: Wait} -> ()
choice2C (&C Wait) = ()

choice1 : Bifurcation -> ()
choice1 (&A (?b ; c)) = choice2B c
choice1 (&A (?b ; c)) = choice2C c

sender : Dual Bifurcation -> ()
sender c = c |> select A |> send True |> select C |> close

_ =
    forkWith sender |> choice1