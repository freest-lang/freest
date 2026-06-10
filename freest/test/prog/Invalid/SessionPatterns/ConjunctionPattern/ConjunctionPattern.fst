module ConjunctionPattern where

type BoolC : 1C
type BoolC = &{True: Wait, False: Wait}

andc : BoolC -> BoolC -1-> Dual BoolC -1-> ()
andc (&True c1)  (&True c2)  c = c |> select True  |> close ; wait c1 ; wait c2
andc (&True c1)  (&False c2) c = c |> select False |> close ; wait c1 ; wait c2
andc (&False c1) (&True c2)  c = c |> select False |> close ; wait c1 ; wait c2
andc (&False c1) c2          c =
  case c2 of
    (&False c2) -> c |> select False |> close ; wait c1 ; wait c2
