{- Semaphores

This implementation guarantees *none* of the following properties:

* requesting a resource and forgetting to release it;
* releasing a resource that was never requested;
* holding a resource for a long time without needing it;
* using a resource without requesting it first (or after releasing it).

https://en.wikipedia.org/wiki/Semaphore_(programming)
-}

module Semaphore where

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
type Semaphore = *?Sem

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
  else case fork_ of &Join _ -> waitFor (n - 1) fork_

-- End of module ForkJoin. An application from here on

-- | A prototypical client entering and leaving a critical region
client : Int -> Semaphore -> Join -> () -1-> ()
client pid sem join _ = 
  case sem |> receive_ |> select SemWait of
    &Go s ->
      putStrLn (show pid ++ " is entering critical region");
      wait s;
      putStrLn (show pid ++ " is leaving critical region");
      receive_ sem |> select SemSignal |> wait;
      select Join join;
      ()

-- | Launch a semaphore server and a few clients
main : ()
main =
  let semClient = launchSemServer 2 in
  let (fork_, join) = channel @(Dual Join) in
  fork (client 1 semClient join);
  fork (client 2 semClient join);
  fork (client 3 semClient join);
  waitFor 3 fork_
