-- The binder `#n` stands for `m`, the first quantifier; the second is another
-- multiplicity variable that merely shares its name. Accepting would turn a
-- linear function into an unrestricted one.
h : forall #m -> forall #n -> (Int -n-> Int) -> Int -m-> Int
h #n f = f

main : ()
main = ()
