module Conjunction where

type BoolC : 1C
type BoolC = &{True: Wait, False: Wait}

andc' : BoolC -> BoolC -1-> Dual BoolC -1-> ()
andc' =
    \(c1 : BoolC) -> case c1 of
        &True  c1 ->
            \(c2 : BoolC) -1-> case c2 of
                &True  c2 ->
                    \(c : Dual BoolC) -1-> c |> select True  |> close ; wait c1 ; wait c2
                &False c2 ->
                    \(c : Dual BoolC) -1->  c |> select False |> close ; wait c1 ; wait c2
        &False c1 ->
            \(c2 : BoolC) -1-> case c2 of
                &True  c2 ->
                    \(c : Dual BoolC) -1->  c |> select False |> close ; wait c1 ; wait c2
                &False c2 ->
                    \(c : Dual BoolC) -1->  c |> select False |> close ; wait c1 ; wait c2

trueC, falseC : Dual BoolC -> ()
trueC  c = c |> select True  |> close
falseC c = c |> select False |> close

toBool : BoolC -> String
toBool (&True  Wait) = "True"
toBool (&False Wait) = "False"

falseAndTrue : ()
falseAndTrue =
    let (c1r, c1w) = channel @BoolC
        (c2r, c2w) = channel @BoolC
        (cr,  cw)  = channel @BoolC
    in fork @() (\(_:()) -1-> trueC  c1w) ;
       fork @() (\(_:()) -1-> falseC c2w) ;
       fork @() (\(_:()) -1-> andc' c1r c2r cw) ;
       print $ toBool cr
