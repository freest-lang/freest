-- The multiplicity of a `forall (a : *T)` must be in scope, as an arrow's must.
g : forall (a : *T) -zz-> a -> a
g x = x

main : ()
main = print @Int (g 5)
