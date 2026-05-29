module LinConsumedInAbstractMultFun where

typeAbs : forall #m -> !Int; Close -> Int -m-> ()
typeAbs #m c x = send x c |> close 

main : ()
main =
  let (o, i) = channel @(!Int; Close)
      closure = typeAbs o
  in fork (\(_ : ()) -1-> receiveAndWait i); closure 1; closure 2