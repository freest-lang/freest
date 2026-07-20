-- A memory cell with non-destructive reads. The cell is process. Read and write
-- operations perform session initiation the cell's (shared) channel. Reading
-- from a memory cell can never block.

type IntCell : *C
type IntCell = *?IntCellSession

type IntCellSession : 1C
type IntCellSession = +{Read: ?Int, Write: !Int} ; Close

write: Int -> IntCell -1-> ForkJoin -1-> ()
write n s j = receive_ s |> select Write |> sendAndClose n ; join j

read: IntCell -> ForkJoin -1-> ()
read s j = let x = receive_ s |> select Read |> receiveAndClose
           in putStrLn ("Read " ++ show x) ; join j

cell : Int -> Dual IntCell -> () -- Void @*T
cell n c =
  case accept c of
    &Write s -> cell (receiveAndWait s) c
    &Read  s -> sendAndWait n s; cell n c

-- Expect 0, 5 or 6
_ =
  let c = forkWith (cell 0)
      (j, a) = channel @ForkJoin in
  fork (\_ -1-> read c j);
  fork (\_ -1-> read c j);
  fork (\_ -1-> write 5 c j); 
  fork (\_ -1-> write 6 c j); 
  fork (\_ -1-> read c j);
  await 5 a