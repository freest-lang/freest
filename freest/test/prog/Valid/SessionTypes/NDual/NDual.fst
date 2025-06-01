module NDual where 

type DD : 1S
-- type DD = Dual (Dual !Int;DD)
type DD = Dual (Dual !Int)

sendInt : forall (a : 1S). DD;a -> a
sendInt @a c = send @Int 5 @a c


rcvInt : forall (a : 1S). (Dual DD);a -> (Int, a)
rcvInt @a c = receive @Int @a c


main : Int
main =
  let (w,r) = channel @(DD;Close) in
  (;) @() @Int
    (fork @() (\(_ : ()) 1-> close (sendInt @Close w)))
    (let (i, r) = rcvInt @Wait r in
    (;) @() @Int (wait r) i)
