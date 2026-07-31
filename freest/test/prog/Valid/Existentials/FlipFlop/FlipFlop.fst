{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
type Counter : *T
type Counter = (exists (a:*T), (a, a -> Int, a -> a))

counter : Counter
counter = ( @Int, ( 0       -- new
                  , id      -- get
                  , succ    -- inc
                  )
          )

type FlipFlop : *T
type FlipFlop = (exists (a:*T), ( a          -- new
                           , a -> Bool -- read
                           , a -> a    -- toggle
                           , a -> a    -- reset
                           )
                )

flipFlop : FlipFlop
flipFlop =
  let (@(a:*T), (new, get, inc)) = counter
  in (@a, ( new        -- new
          , even . get -- read
          , inc        -- toggle
          , \_ -> new  -- reset
          )
     )

_ =
  let (@_, (new, read, toggle, reset)) = flipFlop
  in new |> toggle |> reset |> toggle |> read |> print
