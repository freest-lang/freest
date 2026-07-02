{- An as-pattern `q@(x, y)` references the value as both the whole (`q`) and its
   parts, so it is a use-twice and its type must be inferred unrestricted
   without an annotation. Before as-pattern types were forced `*T`, the tuple
   here inferred `1T` and the as-pattern was rejected ("Non-linear pattern for
   linear type"). -}
module AsPatInferUn where

f : forall a b -> (a, b) -> ((a, b), a)
f @a @b p = case p of q@(x, y) -> (q, x)

main : ()
main = let (pp, z) = f @Int @Int (5, 9) in print z
