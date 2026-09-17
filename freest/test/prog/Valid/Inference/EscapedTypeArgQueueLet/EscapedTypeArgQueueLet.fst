-- Both ends of the queue share the type argument initQueue leaves open; sending binds it.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue () in
  let _ = send_ 5 w in
  print @Int (receive_ r)
