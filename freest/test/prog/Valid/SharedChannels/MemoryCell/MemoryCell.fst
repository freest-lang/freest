-- A memory cell with non-destructive reads. The cell is a process. Read and
-- write operations perform session initiation on the cell's shared channel
-- ('CellRef'), which yields a linear per-interaction session ('CellOp').
-- Reading from a memory cell can never block.

type CellOp : *T -> 1C
type CellOp a = +{Read: ?a, Write: !a} ; Close

type CellRef : *T -> *C
type CellRef a = *?(CellOp a)

write : forall (a : *T) -> a -> CellRef a -1-> ForkJoin -1-> ()
write x s j = receive_ s |> select Write |> sendAndClose x ; join j

read : forall (a : *T) -> CellRef a -> ForkJoin -1-> ()
read s j = let x = receive_ s |> select Read |> receiveAndClose
           in putStrLn ("Read " ++ show x) ; join j

cell : forall (a : *T) -> a -> Dual (CellRef a) -> () -- Void @*T
cell n c =
  case accept c of
    &Write s -> cell (receiveAndWait s) c
    &Read  s -> sendAndWait n s ; cell n c

-- Expect three outputs, composed of 0, 5 or 6 (possibly duplicated)
_ =
  let c = forkWith (cell 0)
      (j, a) = channel @ForkJoin in
  fork (\_ -1-> read    c j);
  fork (\_ -1-> read    c j);
  fork (\_ -1-> write 5 c j);
  fork (\_ -1-> write 6 c j);
  fork (\_ -1-> read    c j);
  await 5 a
