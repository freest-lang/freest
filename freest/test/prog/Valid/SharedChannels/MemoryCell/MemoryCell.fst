-- A memory cell with non-destructive reads. The cell is process. Read and write
-- operations perform session initiation the cell's (shared) channel. Reading
-- from a memory cell can never block.

module MemoryCell where

type IntCell : *C
type IntCell = *?IntCellSession

type IntCellSession : 1C
type IntCellSession = +{Read: ?Int, Write: !Int} ; Close

write: Int -> IntCell 1-> ()
write n s = (receive_ @IntCellSession s) |> select Write |> sendAndClose @Int n 

read: IntCell -> Int
read s = (receive_ @IntCellSession s) |> select Read|> receiveAndClose @Int

cell : Int -> Dual IntCell -> Diverge
cell n c =
  case accept @IntCellSession c of
    &Write s -> cell (receiveAndWait @Int s) c
    &Read s -> sendAndWait @Int n s ; cell n c

sleep : Int -> ()
sleep n = if n == 0 then () else sleep (n - 1)

-- Expect 0, 5 or 6
main: Int
main =
  let c = forkWith @IntCell @() (cell 0) in
  let (r, w) = channel @*?IntCellSession in
  fork (\(_ : ()) 1-> read c);
  fork (\(_ : ()) 1-> read c);
  fork (\(_ : ()) 1-> write 5 c); 
  fork (\(_ : ()) 1-> write 6 c); 
  sleep 10000;
  read c
