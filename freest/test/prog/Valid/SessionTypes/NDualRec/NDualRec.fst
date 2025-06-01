module NDualRec where

type Choice : 1S
type Choice = +{More: !Int;DD, Enough: Close}

type DD : 1S
type DD = Dual (Dual Choice)

sendInt : Int -> DD -> ()
sendInt i c =
  close (select Enough (send @Int (i + 2) @DD (select More (send @Int (i + 1) @DD (select More (send @Int i @DD (select More c)))))))

rcvInt : Int -> Dual DD -> Int
rcvInt acc c =
  case c of
    &Enough c -> (;) @() @Int (wait c) acc
    &More c ->
      let (i, c) = receive @Int @(Dual DD) c in
      rcvInt (acc+i) c

main : Int
main =
  let (w,r) = channel @DD in
  (;) @() @Int
    (fork @() (\(_ : ()) 1-> sendInt 0 w))
    (rcvInt 0 r)
