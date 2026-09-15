-- The let-bound pair keeps initQueue's type argument open and each use re-binds
-- it locally, so an Int is sent and a Char received.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue () in
  let _ = send_ 5 w in
  print @Char (receive_ r)
