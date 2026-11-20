-- The binder `@elem` stands for `elm`, the first quantifier; the second is
-- another variable that merely shares its name.
h : forall elm -> forall elem -> elem -> elm
h @elem x = x

main : ()
main = ()
