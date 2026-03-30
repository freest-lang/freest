module Pmap where

map, pmap : forall (a : 1T) (b : 1T) . (a -> b) -> [a] -> [b]

map @a @b _ [] = [] @b
map @a @b f (x :: xs) = f x :: map f xs

pmap @a @b f xs =
  map (receiveAndWait @b) $ -- CANNOT INFER
    map (\(x : a) -> forkWith1 (sendAndClose (f x))) xs

-- pmap f =
--   map receiveAndWait . map (\x -> forkWith (sendAndClose (f x)))

main : ()
main =
    print (pmap (2 *) ([1, 2, 3, 4, 5] @Int))
