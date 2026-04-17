module PartialSend where

consumeC : !Int;Wait -> ()
consumeC c = send 7 c |> wait

consumeD : !Int;?Bool;Close -> ()
consumeD d = receiveAndClose (send 7 d); ()

f : Bool -> !Int;Wait -> !Int;?Bool;Close 1-> ()
f cond c d =
  let x = send 5 in  -- x : ∀b . !Int;b 1-> b
    if cond
    then x c |> wait; consumeD d
    else receiveAndClose (x d); consumeC c

main : Int
main = 5
