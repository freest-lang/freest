-- Explicit abstraction binders bind their quantifier by position, not by name,
-- and never mix up with the omitted (anonymous) ones.

-- Names the FIRST quantifier `b` (the signature calls it `a`), omitting the
-- second. The body annotation `x : b` therefore pins x to the first quantifier,
-- which type-checks only if the explicit binder and the omitted one stay
-- distinct (a name-based mix-up would make it `x : <second quantifier>`).
firstOf : forall a b -> a -> b -> a
firstOf @b x y = (x : b)

-- Interleaved: omit the first quantifier, name the second, and use that name.
tagSnd : forall a -> a -> forall c -> c -> c
tagSnd x @c z = (z : c)

main : ()
main = print (firstOf 10 True, tagSnd 1 True)
