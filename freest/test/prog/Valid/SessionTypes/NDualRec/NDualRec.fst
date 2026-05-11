module NDualRec where

type Choice : 1C
type Choice = +{More: !Int;DD, Enough: Close}

type DD : 1C
type DD = Dual (Dual Choice)

sendInt : Int -> DD -> ()
sendInt i c =
  c |> select More
    |> send i 
    |> select More
    |> send (i + 1) 
    |> select More 
    |> send (i + 2) 
    |> select Enough
    |> close

rcvInt : Int -> Dual DD -> Int
rcvInt acc c =
  case c of
    &Enough c -> wait c; acc
    &More   c ->
      let (i, c) = receive c in
      rcvInt (acc+i) c

main : Int
main =
  let (w, r) = channel @DD in
  fork #1 (\(_ : ()) -1-> sendInt 0 w); 
  rcvInt 0 r