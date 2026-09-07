{- A `\@a` binder in a definition *body* takes its kind from the quantifier it
   is checked against — here `1C`, as `channel` demands — instead of defaulting
   to `1T`. -}

f : Int -> forall (a : 1C) -> (a, Dual a)
f _ = \@a -> channel @a

main : ()
main = ()

-- the same binder, taking its kind from an ascription rather than a signature
h : ()
h = let _ = ((\@a -> channel @a) : forall (a : 1C) -> (a, Dual a)) in ()
