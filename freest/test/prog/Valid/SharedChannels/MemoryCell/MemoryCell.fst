-- A memory cell with non-destructive reads. The cell is process. Read and write
-- operations perform session initiation the cell's (shared) channel. Reading
-- from a memory cell can never block.

module MemoryCell where

type IntCell : *C
type IntCell = *?IntCellSession

type IntCellSession : 1C
type IntCellSession = +{Read: ?Int, Write: !Int} ; Close

write: Int -> IntCell 1-> ()
write n s = receive_ s |> select Write |> sendAndClose n 

read: IntCell -> Int
read s = receive_ s |> select Read |> receiveAndClose

cell : Int -> Dual IntCell -> Void @*T
cell n c =
  case accept c of
    &Write s -> cell (receiveAndWait s) c
    &Read  s -> sendAndWait n s; cell n c

sleep : Int -> ()
sleep 0 = () 
sleep n = sleep (n - 1)

-- Expect 0, 5 or 6
main: Int
main =
  let c = forkWith (cell 0) in
  let (r, w) = channel @*?IntCellSession in
  fork (\(_ : ()) 1-> read c);
  fork (\(_ : ()) 1-> read c);
  fork (\(_ : ()) 1-> write 5 c); 
  fork (\(_ : ()) 1-> write 6 c); 
  sleep 10000;
  read c
