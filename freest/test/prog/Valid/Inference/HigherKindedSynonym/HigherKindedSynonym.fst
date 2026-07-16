-- A higher-kinded type-synonym signature is inferred regardless of how the arity
-- is written: parameters (App2), a type-level lambda RHS (App), or an application
-- returning an operator (App3). A non-recursive synonym gets a whole-kind-variable
-- initial kind inferred from its body, so a higher-kinded RHS no longer needs a
-- kind signature.
type App  = \(a : *T -> *T) (b : *T) -> a b
type App2 (a : *T -> *T) (b : *T) = a b
type App3 = (\(a : (*T -> *T) -> *T -> *T) -> a) (\(a : *T -> *T) (b : *T) -> a b)
