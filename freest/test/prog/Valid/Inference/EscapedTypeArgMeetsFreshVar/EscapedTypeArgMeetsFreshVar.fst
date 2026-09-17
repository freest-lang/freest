-- The open queue type meets bottom's fresh result variable, which is the one bound.
initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

bottom : forall a -> () -> a
bottom @a _ = undefined @a

main : ()
main =
  let (r, w) = initQueue () in
  let f = \(x:()) -> if True then receive_ r else bottom x in
  let _ = send_ 1 w in
  print @Int (receive_ r)
