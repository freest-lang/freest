module SharedQueue where

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
    send_ i head;
    runHeadNode (receiveAndClose prev) head

runTailNode : Dual Internal -> Dual Tail -1-> ()
runTailNode next tail =
    let i = receive_ tail in
    let (prev', next') = channel @Internal in
    fork (\_ -1-> send i next |> send prev' |> wait);
    runTailNode next' tail
    -- Internal error at Validation.Rename.rename: Dual
    -- runTailNode (fork_ @Internal (\(c : Dual Internal) -> send c (send i next))) tail

-- queue

type Queue : *T
type Queue = (Head, Tail)

initQueue : Queue
initQueue =
    let (internalC, internalS) = channel @Internal in
    (forkWith (runHeadNode internalC),
     forkWith (runTailNode internalS))

enqueue : Int -> Queue -> ()
enqueue i queue = 
    send_ i $ snd queue

dequeue : Queue -> Int
dequeue queue = 
    receive_ $ fst queue

-- counter
type Counter : *C
type Counter = *?Int

runCounter : Int -> Dual Counter -> ()
runCounter i counter =
    send_ i counter;
    runCounter (i + 1) counter

initCounter : Counter
initCounter = 
    let (counterC, counterS) = channel @Counter in
    fork (\_ -1-> runCounter 0 counterS);
    counterC

-- main

maxSize : Int
maxSize = 3

main : ()
main =
    let queue   = initQueue in
    let counter = initCounter in
    -- writer-reader concurrency, no writter-writer nor reader-reader concurrency
    parallel maxSize (\_ -> enqueue (receive_ counter) queue);
    repeat maxSize $ (\_ -> print (dequeue queue))
    -- writer-reader, writter-writer and reader-reader concurrency
    -- parallel @() 10 $ (\(_ : ()) -> enqueue (receiveUn @Int counter) queue);
    -- parallel @() 10 $ (\(_ : ()) -> printIntLn (dequeue queue))
