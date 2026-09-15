-- As ChanTypeConfusionLet, with the pair bound by a case alternative.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  case initQueue () of
    (r, w) -> let _ = send_ 5 w in print @Char (receive_ r)
