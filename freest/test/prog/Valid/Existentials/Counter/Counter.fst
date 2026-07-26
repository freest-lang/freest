{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}
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

listCounter : Counter
listCounter = (@[()], ( []
                      , length
                      , (()::)
                      )
              ) 

incTwice : Counter -> ()
incTwice counter =
  let (@_, (new, get, inc)) = counter
  in new |> inc |> inc |> get |> print

_ = incTwice intCounter ; incTwice listCounter
