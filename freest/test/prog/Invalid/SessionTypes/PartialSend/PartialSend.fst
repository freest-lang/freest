-- `send` is prenex, so `send 5` fixes its continuation where it is bound, and
-- with no let generalisation `x` cannot serve both `!Int;Wait` and
-- `!Int;?Bool;Close`.
consumeC : !Int;Wait -> ()
consumeC c = send 7 c |> wait

consumeD : !Int;?Bool;Close -> ()
consumeD d = receiveAndClose (send 7 d); ()

f : Bool -> !Int;Wait -> !Int;?Bool;Close -1-> ()
f cond c d =
  let x = send 5 in
    if cond
    then x c |> wait; consumeD d
    else receiveAndClose (x d); consumeC c
