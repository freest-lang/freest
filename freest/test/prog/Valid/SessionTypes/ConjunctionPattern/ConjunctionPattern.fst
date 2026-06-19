module Conjunction where

type BoolC : 1C
type BoolC = &{True: Wait, False: Wait}

andc : BoolC -> BoolC -1-> Dual BoolC -1-> ()
andc (&True c1)  (&True c2)  c = c |> select True  |> close ; wait c1 ; wait c2
andc (&True c1)  (&False c2) c = c |> select False |> close ; wait c1 ; wait c2
andc (&False c1) (&True c2)  c = c |> select False |> close ; wait c1 ; wait c2
andc (&False c1) (&False c2) c = c |> select False |> close ; wait c1 ; wait c2

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
       fork @() (\(_:()) -1-> andc c1r c2r cw) ;
       putStrLn $ toBool cr
