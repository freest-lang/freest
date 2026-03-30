{-
Unrestricted send.

The type of send is

  ∀a . a *-> ∀b . !a;b 1-> b

Any value (linear or unrestricted) can be sent.

Using eta-conversion one can write a variant of send that accepts only
unrestricted values. The partially evaluated function can then be reused, contrary to a partially evaluated send.
-}

module USend where

unsend : forall (a : *T). a -> forall (b : 1S). () -> !a;b 1-> b
unsend @a x @b () = send x @b -- CANNOT INFER

main : Int
main =
  let (s1, r1) = channel @(!Int;Close)
      (s2, r2) = channel @(!Int;Close)
      sendFive = unsend 5 in
  fork (\(_ : ()) 1-> close (sendFive () s1));
  fork (\(_ : ()) 1-> close (sendFive () s2));
-- Now let's try with send, rather than unsend:
  -- let sendFive = send @Int 5 @Close in
  -- fork (\(_ : ()) 1-> sendFive s1 |> close);
  -- fork (\(_ : ()) 1-> sendFive s2 |> close);
-- Variable or data constructor not in scope: 'sendFive'
  receiveAndWait r1 + receiveAndWait r2
