map, pmap : forall a b -> (a -> b) -> [a] -> [b]

map @a @b _ [] = [] @b
map @a @b f (x :: xs) = f x :: map f xs

pmap @a @b f xs =
  map receiveAndWait $
    map (\(x : a) -> forkWith (sendAndClose (f x))) xs

_ =
  print (pmap (2 *) ([1, 2, 3, 4, 5]))

{-
Pmap builds an intermediate list of session channels, so it needs
cross-list-kind maps (unrestricted->linear, linear->unrestricted);
not expressible with two monomorphic lists (needs #m kind polymorphism).
-}