-- 1. From Counter.fst

type CounterADT : *T
type CounterADT = (exists a, ( a         -- new
                          , a -> Int  -- get
                          , a -> a    -- inc
                          )
               )

intCounter : CounterADT
intCounter = (@Int, ( 0     -- new
                    , id    -- get
                    , succ  -- inc
                    )
             )
-- End from

type CounterProvider = !CounterADT ; Close

counterProvider : CounterProvider -> ()
counterProvider = sendAndClose intCounter

incTwice : Dual CounterProvider -> ()
incTwice s =
  let (@_, (new, get, inc)) = receiveAndWait s
  in new |> inc |> inc |> get |> print

_ =
    forkWith counterProvider |> incTwice
