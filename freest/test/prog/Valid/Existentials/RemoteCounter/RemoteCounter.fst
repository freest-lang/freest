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

type CounterProviderOneGo = *?CounterADT

counterProviderOneGo : Dual CounterProviderOneGo -> ()
counterProviderOneGo c =
    c |> send_ intCounter |> counterProviderOneGo

incTwice : CounterProviderOneGo -> ()
incTwice s =
  let (@_, (new, get, inc)) = receive_ s
  in new |> inc |> inc |> get |> print

_ = forkWith counterProviderOneGo |> incTwice
