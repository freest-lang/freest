-- The let-bound pair would keep initQueue's type argument open, letting each use
-- re-bind it: an Int sent and a Char received.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue () in
  let _ = send_ 5 w in
  print @Char (receive_ r)
