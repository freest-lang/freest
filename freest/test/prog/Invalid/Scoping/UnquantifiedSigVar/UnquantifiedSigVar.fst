-- A signature with a forall of its own must bind every type variable not in
-- scope: `a` is not implicitly quantified next to `b`.
idImp : forall b -> a -> a
idImp x = x
