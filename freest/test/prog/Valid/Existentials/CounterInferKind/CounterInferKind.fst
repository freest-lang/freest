{- Existential unpack with the binder kind omitted: `@c` (not `@(c : *T)`).
   The kind is inferred from the existential's binder kind at typing. -}
module CounterInferKind where

type Counter : *T
type Counter = (exists (a : *T), (a, a -> Int, a -> a))

counterADT : Counter
counterADT = (@Int, (1, \i -> i, \i -> succ i)) : Counter

main : ()
main =
  let (@c, (new, get, inc)) = counterADT
  in print (get (inc new))
