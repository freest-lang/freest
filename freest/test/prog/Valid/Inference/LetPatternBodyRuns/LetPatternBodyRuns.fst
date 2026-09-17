-- Matching instantiates pairOf, so its body runs at the binding.
pairOf : forall a -> (Maybe a, Int)
pairOf @a = let _ = print @Int 7 in (Nothing, 3)

main : ()
main = let (m, n) = pairOf in print @Int n
