{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
module Counter where

type Counter : *T
type Counter = exists (a : *T) . (a, a -> Int, a -> a)

counterADT : Counter
counterADT = (@Int, ( 1 
                    , \(i : Int) -> i
                    , \(i : Int) -> succ i
                    )
             ) 
           : Counter

main : Int
main =
  let (@c, (new, get, inc)) = counterADT
  in get (inc new)

