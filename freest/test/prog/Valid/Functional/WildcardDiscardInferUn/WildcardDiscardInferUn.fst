{- A component discarded by a wildcard `_` in a destructuring must be inferred
   unrestricted without an annotation: `_` drops the second component, so its
   type is forced `*T` — as an unused named binder already is. -}
module WildcardDiscardInferUn where

fst' : forall a b -> (a, b) -> a
fst' @a @b p = let (x, _) = p in x

main : ()
main = print (fst' @Int @Char (5, 'h'))
