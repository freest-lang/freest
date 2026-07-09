-- Type/multiplicity abstraction binders may be omitted in a function
-- definition; they are reconstructed from the signature.

-- all abstractions omitted
idA : forall a -> a -> a
idA x = x

-- interleaved signature (quantifiers before and after a value parameter)
mkPair : forall #m a -> a -m-> forall c -> c -> (a, c)
mkPair x y = (x, y)

-- name the first type variable, omit the rest
constA : forall a b -> a -> b -> a
constA @a x y = x

-- provide only the multiplicity
appM : forall #m a b -> (a -m-> b) -> a -m-> b
appM #m f x = f x

-- clauses may omit their abstractions differently (same value arity)
pick : forall a -> Bool -> a -> a -> a
pick @a True  x y = x
pick    False x y = y

main : ()
main =
  print ( idA 1
        , mkPair 2 3
        , constA 4 5
        , appM (\x -> x + 1) 6
        , pick True 7 8
        , pick False 7 8 )
