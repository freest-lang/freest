module ErrorPosMessage where

type F : 1S
type F = !Int; Close

f : F -> ()
f c = send 4 c |> close

f1 : Dual F -> (Int, Wait)
f1 c = receive c

main : Int
main =
  let (w, r) = channel @(!Bool;Close) in
  fork #1 (\(_ : ()) -1-> f w);
  let (x, c) = f1 r in
  wait c;
  x
