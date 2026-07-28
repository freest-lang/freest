{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
type Counter : *T
type Counter = (exists a, (a, a -> Int, a -> a))

counter : Counter
counter = ( @Int, ( 0       -- new
                  , id      -- get
                  , succ    -- inc
                  )
          )

type FlipFlop : *T
type FlipFlop = (exists a, ( a          -- new
                           , a -> Bool -- read
                           , a -> a    -- toggle
                           , a -> a    -- reset
                           )
                )

flipFlop : FlipFlop
flipFlop = ( @c, ( new        -- new
                 , even . get -- read
                 , inc        -- toggle
                 , \_ -> new  -- reset
                 )
            )
  where (@c, (new, get, inc)) = counter

_ = new |> toggle |> reset |> toggle |> read |> print
  where (@f, (new, read, toggle, reset)) = flipFlop
