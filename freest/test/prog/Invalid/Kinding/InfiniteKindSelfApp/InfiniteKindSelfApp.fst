{- Self-application `f f` with `f`'s kind left to inference: the inferred kind
   would be infinite (`κ = κ -> κ'`). Must fail cleanly (occurs check), not
   diverge — regression guard for the solver non-termination bug. -}
foo : (forall f -> f f) -> ()
foo _ = ()
