-- From Counter.fst
type Counter : *T
type Counter = (exists a, ( a         -- new
                          , a -> Int  -- get
                          , a -> a    -- inc
                          )
               )

intCounter : Counter
intCounter = (@Int, ( 0     -- new
                    , id    -- get
                    , succ  -- inc
                    )
             ) 

-- listCounter : Counter
-- listCounter = (@[()], ( []
--                       , length
--                       , (()::)
--                       )
--               ) 
-- End from

type CounterProvider = *?Counter

counterProvider : Dual CounterProvider -> Void @*T
counterProvider c =
    c |> accept |> send intCounter |> counterProvider

-- incTwice : CounterProvider -> ()
-- incTwice s =
--   let (@_, (new, get, inc)) = receive_ s
--   in new |> inc |> inc |> get |> print

-- _ =
--     forkWith @