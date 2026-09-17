-- ids' element type is polymorphic, and the queue's open element type must be a
-- monotype, so its type argument has to be written.
mkq : forall a -> () -> (*?[a], *![a])
mkq @a _ = channel @(*?[a])

ids : [forall a -> a -> a]
ids = [id]

main : ()
main =
  let (r, w) = mkq () in
  let _ = send_ ids w in
  print @Int 1
