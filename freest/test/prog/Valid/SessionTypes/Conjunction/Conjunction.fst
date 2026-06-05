module Conjunction where

type BoolC : 1S
type BoolC = &{True: Wait, False: Wait}

andc : BoolC -> BoolC -1-> Dual BoolC -1-> ()
andc (&True _)  (&True _)  c = c |> select True  |> close
andc (&True _)  (&False _) c = c |> select False |> close
andc (&False _) (&True _)  c = c |> select False |> close
andc (&False _) (&False _) c = c |> select False |> close

andc' : BoolC -> BoolC -1-> Dual BoolC -1-> ()
andc' c1 c2 c =
    case c1 of
        &True  c1 ->
            (case c2 of
                &True  _ -> c |> select True  |> close
                &False _ -> c |> select False |> close) ;
            wait c1 ;
            wait c2
        &False _ ->
            (case c2 of
                &True  _ -> c |> select False |> close
                &False _ -> c |> select False |> close) ;
            wait c1 ;
            wait c2

trueC, falseC : Dual BoolC ; Close -> ()
trueC  c = c |> select True  |> close
falseC c = c |> select False |> close


falseAndTrue : ()
falseAndTrue =
    let (c1r, c1w) = channel @(BoolC ; Wait)
        (c2r, c2w) = channel @(BoolC ; Wait)
        (cr,  cw)  = channel @(BoolC ; Wait)
    in fork @() (\(_:()) -1-> trueC  c1w) ;
       fork @() (\(_:()) -1-> falseC c2w) ;
       andc c1r c2r cr
