-- The control for ChanTypeConfusionCase.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  case initQueue @Int () of
    (r, w) -> let _ = send_ 5 w in print @Char (receive_ r)
