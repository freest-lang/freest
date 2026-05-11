module NDual where 

type DD : 1S
-- type DD = Dual (Dual !Int;DD)
type DD = Dual (Dual !Int)

sendInt : forall (a : 1S) -> DD; a -> a
sendInt @a c = send 5 c


rcvInt : forall (a : 1S) -> (Dual DD); a -> (Int, a)
rcvInt @a c = receive c


main : Int
main =
  let (w,r) = channel @(DD; Close) in
  fork #1 (\(_ : ()) -1-> w |> sendInt |> close);
  let (i, r) = rcvInt r in
  wait r;
  i
