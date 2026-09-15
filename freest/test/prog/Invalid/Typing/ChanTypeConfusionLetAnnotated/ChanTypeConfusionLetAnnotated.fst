-- The control for ChanTypeConfusionLet: with the type argument written, receiving
-- a Char from an Int queue is a type error.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue @Int () in
  let _ = send_ 5 w in
  print @Char (receive_ r)
