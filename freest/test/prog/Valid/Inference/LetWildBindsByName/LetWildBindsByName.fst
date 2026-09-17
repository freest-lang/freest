-- A wildcard matches nothing, so pairOf is not instantiated and its body never runs.
pairOf : forall a -> (Maybe a, Int)
pairOf @a = let _ = print @Int 7 in (Nothing, 3)

main : ()
main = let _ = pairOf in print @Int 1
