module InferredDeclKinds where

-- Declaration-kind inference (no kind signatures): the alias `Pair` is
-- inferred to have kind `*T -> *T -> *T` and `Count` the kind `*T`, from the
-- shapes of their bodies alone.
type Count = Int
type Pair a b = (a, b)

fst' : Pair Int Count -> Int
fst' p = let (x, _) = p in x

main : ()
main = print (fst' (7, 35))
