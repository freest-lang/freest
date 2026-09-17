-- g 5 is a suspension: instantiating it never returns. A parameter whose type is
-- written polymorphic, like h's, receives it uninstantiated; so does a parameter
-- whose type is a bare variable, like discard's, when the callee's type argument
-- is written. Without that argument, g 5 would be instantiated where it is passed.
g : Int -> forall a -> Int
g x @a = g x @a

h : (forall a -> Int) -> Int
h _ = 0

discard : forall b -> b -> ()
discard _ = ()

main : ()
main = discard @(forall a -> Int) (g 5); print (h (g 5))
