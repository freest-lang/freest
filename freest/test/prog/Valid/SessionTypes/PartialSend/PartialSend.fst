module PartialSend where

consumeC : !Int;Wait -> ()
consumeC c = send 7 c |> wait

consumeD : !Int;?Bool;Close -> ()
consumeD d = receiveAndClose @Bool (send 7 d); ()

f : Bool -> !Int;Wait -> !Int;?Bool;Close 1-> ()
f cond c d =
  let x = send @Int 5 in  -- x : ∀b . !Int;b 1-> b
    if cond
    then x @Wait c |> wait; consumeD d
    else receiveAndClose @Bool (x @(?Bool;Close) d); consumeC c

main : Int
main = 5
