-- discard's parameter type is a bare variable, so f 5 is instantiated where it is
-- passed, and the abstraction's body runs there.
f : Int -> forall a -> Int
f x @a = let _ = print @Int 7 in x

discard : forall b -> b -> ()
discard _ = ()

main : ()
main = discard (f 5); print @Int 1
