type Provide a = &{New : !a ; Provide a, Get: !(a -> Int) ; Provide a,  Inc: !(a -> a) ; Provide a, Done: Wait}

type CounterProvider = !type a. Provide a

counterProvider : CounterProvider -> ()
counterProvider c = 
  c |> sendType @Int |> provide
  where
    provide : Provide Int -> ()
    provide (&New  c) = c |> send 0                |> provide
    provide (&Get  c) = c |> send id |> provide
    provide (&Inc  c) = c |> send succ             |> provide
    provide (&Done c) = c |> wait

incTwice : Dual CounterProvider -> ()
incTwice c =
  let (@a, c) = receiveType c
      (inc, c) = c |> select Inc  |> receive @(a -> a) @(Dual (Provide a))
      (new, c) = c |> select New  |> receive
      (get, c) = c |> select Get  |> receive
      ()       = c |> select Done |> close
  in new |> inc |> inc |> get |> print

_ = forkWith counterProvider |> incTwice