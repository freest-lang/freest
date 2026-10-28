-- A memory cell with non-destructive reads. The cell is a process. Read and
-- write operations perform session initiation on the cell's shared channel
-- ('CellRef'), which yields a linear per-interaction session ('CellOp').
-- Reading from a memory cell can never block.
--
-- A deterministic version of 'MemoryCell': rather than printing, the reader
-- threads send the values they read back to the main thread, which checks them.

type CellOp : *T -> 1C
type CellOp a = +{Read: ?a, Write: !a} ; Close

type CellRef : *T -> *C
type CellRef a = *!(Dual (CellOp a))

-- clients
write : forall (a : *T) -> a -> CellRef a -> ()
write x s = request s |> select Write |> sendAndClose x

read : forall (a : *T) -> CellRef a -> a
read s = request s |> select Read |> receiveAndClose

-- servers I _ using accept
cell : forall (a : *T) -> a -> Dual (CellRef a) -> ()
cell n s =
  case accept s of
    &Write c -> cell (receiveAndWait c) s
    &Read  c -> sendAndWait n c ; cell n s

-- servers II _ using runServer
cell' : forall (a : *T) -> a -> Dual (CellRef a) -> Void @*T
cell' @a =
  runServer serveOne
  where
    serveOne : forall a -> a -> Dual (CellOp a) -> a
    serveOne _ (&Write c) = receiveAndWait c
    serveOne x (&Read  c) = sendAndWait x c ; x

-- | Collect the three values read (on channel r) and check that they make
-- sense.
test : *?Int -> ()
test r =
  if check (receive_ r) (receive_ r) (receive_ r)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | The cell starts at 0 and is written 5 and 6, in any order; hence each
    -- value read is one of 0, 5 or 6 (possibly repeated).
    valid : Int -> Bool
    valid n = n == 0 || n == 5 || n == 6
    -- | Do the three values read make sense?
    check : Int -> Int -> Int -> Bool
    check x y z = valid x && valid y && valid z

-- Multiple Producer, Single Consumer (mpsc)

-- Readers report the values read on a shared channel (receiving three values
-- tells main that the readers are done); writers signal completion on a
-- fork-join channel.
main : ()
main =
  let c      = forkWith (cell 0)
      (j, a) = channel @ForkJoin
      (r, w) = channel @(*?Int) in
  fork (\_ -> send_ (read c) w ; ()) ;
  fork (\_ -> send_ (read c) w ; ()) ;
  fork (\_ -> c |> write 5 ; join j) ;
  fork (\_ -> c |> write 6 ; join j) ;
  fork (\_ -> send_ (read c) w ; ()) ;
  await 2 a ;
  test r
