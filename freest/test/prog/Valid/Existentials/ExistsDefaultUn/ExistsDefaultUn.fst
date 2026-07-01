{- An omitted functional-existential binder defaults to unrestricted (*T), dual
   to a forall binder's most-general 1T: the existential is covariant in the
   binder kind, so *T is the most-usable default and lets the unpacked abstract
   value be used more than once without an annotation. (A *linear* existential
   is the annotated case `exists (a:1T)`.) -}
module ExistsDefaultUn where

type Counter = (exists a, (a, a -> Int, a -> a))

counterADT : Counter
counterADT = (@Int, (1, \i -> i, \i -> succ i)) : Counter

main : ()
main =
  let (@c, (new, get, inc)) = counterADT
  in print (get (inc new) + get new)          -- `new` used twice => needs a : *T
