-- `pair`'s `a` is its own, implicitly quantified: `g`'s is not in scope
-- without a binder. Equal names must not make the two equivalent.
g : a -> Bool
g x = not (fst (pair @Bool 0))
  where
    pair : Int -> (a, a)
    pair _ = (x, x)

main : ()
main = ()
