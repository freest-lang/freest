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

-- 2. The counter transmited in one go

type CounterProviderOneGo = *?CounterADT

counterProviderOneGo : Dual CounterProviderOneGo -> ()
counterProviderOneGo c =
    c |> send_ intCounter |> counterProviderOneGo

incTwice : CounterProviderOneGo -> ()
incTwice s =
  let (@_, (new, get, inc)) = receive_ s
  in new |> inc |> inc |> get |> print

_ = forkWith counterProviderOneGo |> incTwice

-- 3. The counter transmited as you go

type C a = &{New: !a ; C a, Get: !(a -> Int) ; C a , Inc: !(a -> a) ; C a , Done: Wait}
type RemoteCounter = (exists a, C a)

type CounterProvider = *?RemoteCounter

forkWith_ : forall #m (a : 1C) -> *!a -> (Dual a -m-> ()) -> ()
forkWith_ #m @a c f =
    fork (\_ -1-> f (accept c))
--   let (x, y) = channel @a in
--   fork (\_ -1-> f y);
--   x

counterProvider : Dual CounterProvider -> ()
counterProvider c = forkWith_ c go
    where
        go : C a
        go (&New s) -> s |> send 0 
    &Get s ->
    &Inc s ->
    &Done s -> wait s