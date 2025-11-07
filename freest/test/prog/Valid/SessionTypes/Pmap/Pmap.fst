module Pmap where

map, pmap : forall (a:1T) . forall (b:1T) . (a -> b) -> [a] -> [b]

map @a @b _ [] = [] @b
map @a @b f (x::xs) = (f x) :: map @a @b f xs

pmap @a @b f xs =
  map @(?b ; Wait) @b (receiveAndWait @b) $
    map @a @(?b ; Wait) (\(x:a) -> forkWith @(?b ; Wait) @() (sendAndClose @b (f x))) xs

-- pmap f =
--   map receiveAndWait . map (\x -> forkWith (sendAndClose (f x)))

main : ()
main =
    print @[Int] (pmap @Int @Int (2*) [1, 2, 3, 4, 5] @ Int)
