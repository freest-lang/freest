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
  let (@a, (new, get, inc)) = counter
  in new |> inc |> inc |> get |> print

incTwiceAnnotated : Counter -> ()
incTwiceAnnotated counter =
  let (@a, (new, get, inc)) = counter
  in (new : a)        |> 
     (inc : a -> a)   |>
     (inc : a -> a)   |>
     (get : a -> Int) |>
     print


_ = incTwice intCounter ; incTwice listCounter
