-- A leading multiplicity forall counts as the signature's own forall, so it
-- must bind `a` too.
k : forall #m -> (a -m-> a) -> a -m-> a
k f x = f x
