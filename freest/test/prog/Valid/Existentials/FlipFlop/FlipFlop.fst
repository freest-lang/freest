{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
type Counter : *T
type Counter = (exists a, (a, a -> Int, a -> a))

counterADT : Counter
counterADT = 
  ( @Int
  , ( 0       -- new
    , id      -- get
    , succ    -- inc
    )
  )

type FlipFlop : *T
type FlipFlop = (exists a, (a, a -> Bool, a -> a, a -> a))

flipFlopADT : FlipFlop
flipFlopADT = 
  ( @c 
  , ( new                -- new
    , \c -> even (get c) -- read
    , \c -> inc c        -- toggle
    , \c -> new          -- reset
    )
  )
  where (@(c : *T), (new, get, inc)) = counterADT

main : ()
main = new |> toggle |> reset |> toggle |> read |> print
  where (@f, (new, read, toggle, reset)) = flipFlopADT
