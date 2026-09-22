-- A memory cell with non-destructive reads. The cell is a process. Read and
-- write operations perform session initiation on the cell's shared channel
-- ('CellRef'), which yields a linear per-interaction session ('CellOp').
-- Reading from a memory cell can never block.

type CellOp : *T -> 1C
type CellOp a = +{Read: ?a, Write: !a} ; Close

type CellRef : *T -> *C
type CellRef a = *?(CellOp a)

-- clients
write : forall (a : *T) -> a -> CellRef a -> ()
write x s = receive_ s |> select Write |> sendAndClose x

read : forall (a : *T) -> CellRef a -> a
read s = receive_ s |> select Read |> receiveAndClose

-- servers I _ using accept
cell : forall (a : *T) -> a -> Dual (CellRef a) -> ()
cell n c =
  case accept c of
    &Write s -> cell (receiveAndWait s) c
    &Read  s -> sendAndWait n s ; cell n c

-- servers II _ using runServer

cell : forall (a : *T) -> a -> Dual (CellRef a) -> ()
cell @a =
  runServer serveOne
  where
    serveOne : forall a -> a -> Dual (CellOp a) -> a
    serveOne _ (&Write c) = receiveAndWait c
    serveOne x (&Read  c) = sendAndWait x c ; x

-- Multiple Producer, Single Consumer (mpsc)

-- Expect three numbers, taken from {0, 5, 6}, possibly duplicated or triplicated_ =
_ =
  let c      = forkWith (cell 0)
      (j, a) = channel @ForkJoin in
  fork (\_ -> c |> read |> print ; join j) ;
  fork (\_ -> c |> read |> print ; join j) ;
  fork (\_ -> c |> write 5       ; join j) ;
  fork (\_ -> c |> write 6       ; join j) ;
  fork (\_ -> c |> read |> print ; join j) ;
  await 5 a

-- Multiple Producer, Multiple Consumer (mpmc)
-- Deadlocks
-- _ =
--   let (c, r) = channel @(CellRef Int)
--       (j, a) = channel @ForkJoin in
--   fork (\_ -> cell r) ;
--   fork (\_ -> cell r) ;
--   fork (\_ -> c |> read |> print ; join j) ;
--   fork (\_ -> c |> read |> print ; join j) ;
--   fork (\_ -> c |> write 5       ; join j) ;
--   fork (\_ -> c |> write 6       ; join j) ;
--   fork (\_ -> c |> read |> print ; join j) ;
--   await 5 a

