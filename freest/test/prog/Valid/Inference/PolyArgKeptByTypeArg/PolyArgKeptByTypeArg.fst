-- As PolyArgInstantiatedWherePassed, with discard's type argument written: f 5 is
-- passed uninstantiated, so its body never runs.
f : Int -> forall a -> Int
f x @a = let _ = print @Int 7 in x

discard : forall b -> b -> ()
discard _ = ()

main : ()
main = discard @(forall a -> Int) (f 5); print @Int 1
