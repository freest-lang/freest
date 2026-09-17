-- One open type argument is bound to a type mentioning another, bound later.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r1, w1) = initQueue () in
  let (r2, w2) = initQueue () in
  let _ = send_ r1 w2 in
  let _ = send_ 5 w1 in
  print @Int (receive_ (receive_ r2))
