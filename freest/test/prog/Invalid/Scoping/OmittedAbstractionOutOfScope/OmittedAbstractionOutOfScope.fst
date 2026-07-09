-- An omitted (reconstructed) abstraction binder is anonymous: it is not in
-- scope in the body, so the annotation `x : a` cannot name it.
g : forall a -> a -> a
g x = (x : a)
