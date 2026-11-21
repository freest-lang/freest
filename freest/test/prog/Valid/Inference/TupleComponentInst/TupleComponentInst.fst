-- A tuple's components are the arguments of a tuple constructor: a polymorphic
-- one (`id`, `[]`) is instantiated, not bound to `a` as it stands, so the order
-- of the components does not matter.
first : forall (a : *T) -> (a, a) -> a
first (x, _) = x

main : ()
main =
  print ((first (succ, id)) 5);
  print (length (first ([5], [])))
