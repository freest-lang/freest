-- `a` is bound by both components of the pair. The annotated lambda says
-- `Int -> Int`, `id` says nothing; whichever comes first, the two bindings
-- must be unified, not one of them dropped.
useFirst : forall (a : *T) -> (a, a) -> (a -> Int) -> Int
useFirst (x, _) f = f x

main : ()
main =
  print (useFirst ((\(x : Int) -> x + 1), id) (\g -> g 1));
  print (useFirst (id, (\(x : Int) -> x + 1)) (\g -> g 1))
