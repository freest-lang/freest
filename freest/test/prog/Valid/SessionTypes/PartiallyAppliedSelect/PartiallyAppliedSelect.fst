module PartiallyAppliedSelect where

type T : 1S
type T = +{A: !Int, B: ?Int}

main : ()
main = 
  let (o, i) = channel @(T;Close) in
  o |> select A |> sendAndClose 5;
  case i of &A i -> i |> receiveAndWait; ()
            &B i -> i |> sendAndWait 5