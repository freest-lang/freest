{- An omitted functional-existential binder is inferred; nothing here forces it
   below unrestricted (*T), which is where an out-polarity binder settles when
   unconstrained — it is covariant, so *T is the most usable choice for whoever
   unpacks it, dual to a forall binder's most-general 1T. Here the unpacked
   value is used twice, which needs *T anyway. A binder a witness forces linear
   is `ExistsLinearWitness`. -}
type Counter = (exists a, (a, a -> Int, a -> a))

counterADT : Counter
counterADT = (@Int, (1, \i -> i, \i -> succ i)) : Counter

main : ()
main =
  let (@c, (new, get, inc)) = counterADT
  in print (get (inc new) + get new)          -- `new` used twice => needs a : *T
