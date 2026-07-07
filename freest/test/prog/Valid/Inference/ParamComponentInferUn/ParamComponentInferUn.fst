{- A value bound in a complex *parameter* pattern (here a tuple) and then
   discarded forces its type unrestricted, so the omitted `forall` binder is
   inferred `*T` — no annotation needed, matching a bare-variable parameter
   destructured in the body. -}
second : forall a -> (a, Int) -> Int
second @a (x, n) = n
