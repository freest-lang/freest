-- A free type variable in a signature is not implicitly quantified; it must be
-- bound by an explicit forall, so `a` here is out of scope.
idImp : a -> a
idImp x = x
