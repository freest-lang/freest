{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
type Counter : *T
type Counter = (exists a, (a, a -> Int, a -> a))

counterADT : Counter
counterADT = (@Int, ( 1 
                    , \i -> i
                    , \i -> succ i
                    )
             ) 
           : Counter

main : ()
main =
  let (@c, (new, get, inc)) = counterADT
  in print (get (inc new))
