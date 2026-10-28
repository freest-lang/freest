-- channel types

type Head, Tail : *C
type Head = {- Dequeue -} *?Int
type Tail = {- Enqueue -} *!Int

type Internal : 1C
type Internal = ?Int; ?Internal; Close 

-- nodes

runHeadNode : Internal -> Dual Head -1-> ()
runHeadNode prev head = 
    let (i, prev) = receive prev in
    head |> send_ i |> runHeadNode (receiveAndClose prev)

runTailNode : Dual Internal -> Dual Tail -1-> ()
runTailNode next tail =
    let i = receive_ tail in
    runTailNode (forkWith (\prev -1-> next |> send i |> send prev |> wait)) tail

-- queue

type Queue : *T
type Queue = (Head, Tail)

initQueue : Queue
initQueue =
    let (internalC, internalS) = channel @Internal in
    (forkWith (runHeadNode internalC),
     forkWith (runTailNode internalS))

enqueue : Int -> Queue -> Tail
enqueue i queue =
    send_ i (snd queue)

dequeue : Queue -> Int
dequeue queue = 
    receive_ $ fst queue

-- counter
type Counter : *C
type Counter = *?Int

runCounter : Int -> Dual Counter -> ()
runCounter i counter =
    counter |> send_ i |> runCounter (i + 1)

initCounter : Counter
initCounter = 
    let (counterC, counterS) = channel @Counter in
    fork (\_ -1-> runCounter 0 counterS);
    counterC

-- main

maxSize : Int
maxSize = 3

-- | Dequeue three values and check that they make sense.
test : Queue -> ()
test queue =
  if check (dequeue queue) (dequeue queue) (dequeue queue)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | The counter hands out 0, 1 and 2, one to each writer
    valid : Int -> Bool
    valid n = 0 <= n && n < maxSize
    -- | Each value enqueued is dequeued exactly once, in any order (the writers
    -- run concurrently)
    check : Int -> Int -> Int -> Bool
    check x y z =
      valid x && valid y && valid z && x /= y && y /= z && x /= z

_ =
    let queue   = initQueue in
    let counter = initCounter in
    -- writer-reader concurrency, no writter-writer nor reader-reader concurrency
    parallel maxSize (\_ -> enqueue (receive_ counter) queue);
    test queue
    -- writer-reader, writter-writer and reader-reader concurrency
    -- parallel @() 10 $ (\(_ : ()) -> enqueue (receiveUn @Int counter) queue);
    -- parallel @() 10 $ (\(_ : ()) -> printIntLn (dequeue queue))
