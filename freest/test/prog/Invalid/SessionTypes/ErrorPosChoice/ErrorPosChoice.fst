module ErrorPosChoice where

type F : 1S
type F = +{B: !Bool; Close}

f : F -> ()
f c = let c = select B c in send True c |> close

f1 : Dual F -> (Bool, Wait)
f1 c = case c of &B c -> receive c

main : Bool
main =
  let (w, r) = channel @(&{B: !Bool};Close) in
  fork #1 (\(_ : ()) -1-> f w);
  let (x, c) = f1 r in
  wait c;
  x



