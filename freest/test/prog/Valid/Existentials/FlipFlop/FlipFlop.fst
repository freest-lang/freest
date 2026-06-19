{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
module FlipFlop where

type Counter : *T
type Counter = (exists (a : *T), (a, a -> Int, a -> a))

counterADT : Counter
counterADT = 
  ( @Int
  , ( 1                    -- new
    , \(i : Int) -> i      -- get
    , \(i : Int) -> succ i -- inc
    )
  ) 
  : Counter

type FlipFlop : *T
type FlipFlop = (exists (a : *T), (a, a -> Bool, a -> a, a -> a))

flipFlopADT : FlipFlop
flipFlopADT = 
  ( @c 
  , ( new                      -- new
    , \(c : c) -> even (get c) -- read
    , \(c : c) -> inc c        -- toggle
    , \(c : c) -> new          -- reset
    )
  ) 
  : FlipFlop
  where (@(c : *T), (new, get, inc)) = counterADT

main : ()
main = print (read (toggle (reset (toggle new))))
  where (@(f : *T), (new, read, toggle, reset)) = flipFlopADT
