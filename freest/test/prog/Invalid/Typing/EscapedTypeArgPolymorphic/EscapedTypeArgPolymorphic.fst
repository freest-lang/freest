-- undefined is passed as a polymorphic value, not instantiated, so the queue's element type cannot be taken from it.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue () in
  let _ = send_ (undefined) w in
  let _ = send_ (undefined) w in
  let x = receive_ r in
  let y = receive_ r in
  print @Int x; print @Int y
