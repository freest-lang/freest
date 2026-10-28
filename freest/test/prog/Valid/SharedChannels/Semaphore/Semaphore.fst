{- Semaphores

This implementation guarantees *none* of the following properties:

* requesting a resource and forgetting to release it;
* releasing a resource that was never requested;
* holding a resource for a long time without needing it;
* using a resource without requesting it first (or after releasing it).

https://en.wikipedia.org/wiki/Semaphore_(programming)
-}

-- Start of module Semaphore

-- | A queue for clients waiting on a semaphore

type WaitAck : 1C
type WaitAck = &{Go: Wait}

type SemQueue : 1T
data SemQueue = Empty () | Head (Dual WaitAck) SemQueue

-- | Enqueue a semaphore client on a given queue
enqueue : Dual WaitAck -> SemQueue -1-> SemQueue
enqueue x (Empty _)  = Head x (Empty ())
enqueue x (Head y q) = Head y (enqueue x q)

-- | Dequeue a semaphore client from a given queue
dequeue : SemQueue -> (Dual WaitAck, SemQueue)
dequeue (Head x q) = (x, q)

-- | The type of semaphores
type Sem : 1C
type Sem = +{SemWait: WaitAck, SemSignal: Wait}

type Semaphore : *C
type Semaphore = *!(Dual Sem)

-- | A semaphore server with a given number of resources and a list of waiting
-- clients
semaphore : Int -> SemQueue -> Dual Semaphore -1-> Void @*T
semaphore n queue sem =
  case accept sem of
    &SemWait s ->
      if n <= 0
        then semaphore (n - 1) (enqueue s queue) sem
        else close (select Go s) ; semaphore (n - 1) queue sem
    &SemSignal s ->
      close s;
      if n < 0
        then let (s', queue) = dequeue queue in
          close (select Go s');
          semaphore (n + 1) queue sem
        else semaphore (n + 1) queue sem

-- | Launch a semaphore for a given number of resources. Returns a channel end
-- to be used by clients. This is the only function exported by this "module".
launchSemServer : Int -> Semaphore
launchSemServer n = forkWith (semaphore n (Empty ()))

-- End of module Semaphore

-- Start of module ForkJoin
type Join : *C
type Join = *+{Join}

waitFor : Int -> Dual Join -> ()
waitFor n fork_ =
  if n == 0
  then ()
  else case fork_ of *&Join -> waitFor (n - 1) fork_

-- End of module ForkJoin. An application from here on

-- | A prototypical client entering and leaving a critical region. Rather than
-- printing, the client reports pid when entering and -pid when leaving.
client : Int -> Semaphore -> Join -> *!Int -> () -1-> ()
client pid sem join report _ =
  case sem |> request |> select SemWait of
    &Go s ->
      send_ pid report;
      wait s;
      send_ (-pid) report;
      request sem |> select SemSignal |> wait;
      select_ Join join;
      ()

-- | Collect the six events of the three clients (on channel c) and check that
-- they make sense.
test : *?Int -> ()
test c =
  if replay 0 0 0 (receiveN 6)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | Receive n events, in order of arrival
    receiveN : Int -> [Int]
    receiveN n
      | n == 0    = []
      | otherwise = receive_ c :: receiveN (n - 1)
    -- | The state of client pid after event e: 0 before entering, 1 inside the
    -- critical region, 2 after leaving, 3 after an impossible event
    step : Int -> Int -> Int -> Int
    step pid e s
      | e ==  pid && s == 0   = 1
      | e == -pid && s == 1   = 2
      | e == pid || e == -pid = 3
      | otherwise             = s
    -- | One for a client inside the critical region, zero otherwise
    inside : Int -> Int
    inside s = if s == 1 then 1 else 0
    -- | Replay the events: each client enters and then leaves, and there are
    -- never more than two clients (the semaphore's resources) inside. A client
    -- reports entering after it enters and leaving before it leaves, so the
    -- replay never counts more clients inside than there actually are.
    replay : Int -> Int -> Int -> [Int] -> Bool
    replay s1 s2 s3 [] = s1 == 2 && s2 == 2 && s3 == 2
    replay s1 s2 s3 (e :: es) =
      let t1 = step 1 e s1
          t2 = step 2 e s2
          t3 = step 3 e s3 in
      inside t1 + inside t2 + inside t3 <= 2 && replay t1 t2 t3 es

-- | Launch a semaphore server and a few clients. Clients report their events on
-- a shared channel and signal completion on a fork-join channel.
main : ()
main =
  let semClient               = launchSemServer 2
      (awaitEnd, joinEnd)     = channel @(Dual Join)
      (collectEnd, reportEnd) = channel @(*?Int) in
  fork (client 1 semClient joinEnd reportEnd);
  fork (client 2 semClient joinEnd reportEnd);
  fork (client 3 semClient joinEnd reportEnd);
  waitFor 3 awaitEnd;
  test collectEnd
