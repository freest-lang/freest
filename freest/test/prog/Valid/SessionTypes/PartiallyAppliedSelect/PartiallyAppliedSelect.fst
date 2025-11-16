module PartiallyAppliedSelect where

type T : 1S
type T = +{A: !Int, B: ?Int}

(|>) : forall (a b : 1T). a -> (a 1-> b) 1-> b
(|>) @a @b x f = f x

main : ()
main = 
  let (o,i) = channel @(T;Close) in
  ((|>) @(!Int;Close) @() ((|>) @(T;Close) @(!Int;Close) o (select A)) (sendAndClose @Int 5));
  -- o |> select A |> sendAndClose @Int 5
  case i of &A i -> i |> receiveAndWait @Int; ()
            &B i -> i |> sendAndWait @Int 5