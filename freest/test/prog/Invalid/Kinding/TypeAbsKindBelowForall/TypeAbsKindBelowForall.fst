-- The abstraction assumes `a : *T` and drops its argument, but the signature lets
-- callers instantiate `a` at a linear type.
f : forall (a : 1T) -> a -> ()
f = \@(a : *T) -> \_ -> ()

main : ()
main = ()
