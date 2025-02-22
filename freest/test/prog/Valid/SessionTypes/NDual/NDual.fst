module NDual where 

type DD : 1S
-- type DD = Dual (Dual !Int;DD)
type DD = Dual (Dual !Int)

sendInt : DD;a -> a
sendInt c = send 5 c


rcvInt : (Dual DD);a -> (Int, a)
rcvInt c = receive c


main : Int
main =
  let (w,r) = channel @(DD;Close) in
  fork @() (\_:()1-> sendInt @Close w |> close);
  let (i, r) = rcvInt @Wait r in
  wait r;
  i
