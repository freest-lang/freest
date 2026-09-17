-- A variable pattern binds pairOf by name: nothing is instantiated, so its body never runs.
pairOf : forall a -> (Maybe a, Int)
pairOf @a = let _ = print @Int 7 in (Nothing, 3)

main : ()
main = let p = pairOf in print @Int 1
