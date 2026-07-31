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
-- End from

type Provide a = +{New : !a ; Provide a, Get: !(a -> Int) ; Provide a,  Succ: !(a -> a) ; Provide a, Done: Close}

type CounterProvider = !type a. Provide a

incTwice : Dual CounterProvider -> ()
incTwice c =
  let (@a, c) = receiveType c
      (counter, c) = c |> select New |> receive
      () = c |> select Done |> wait in
  ()
--   let (@_, (new, get, inc)) = receiveAndWait s
--   in new |> inc |> inc |> get |> print

-- _ =
--     forkWith counterProvider |> incTwice