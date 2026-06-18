-- A memory cell with destructive reads. The successive values of the cell are
-- messages in transit. A read operation reads one such message, thus "clearing"
-- the contents of the cell. In this way reading from a memory cell may be a
-- blocking operation. Works only with no less writes than reads, properly
-- interleaved.
module MemoryCellDestructive where

type IntCell : *C
type IntCell = *!Int

write: Int -> IntCell -1-> ()
write = send_

read: Dual IntCell -> Int
read = receive_

sleep : Int -> ()
sleep n = if n == 0 then () else sleep (n - 1)

main: Int
main =
  let (w, r) = channel @IntCell in
  fork (\(_ : ()) -1-> read r);
  fork (\(_ : ()) -1-> read r);
  fork (\(_ : ()) -1-> write 4 w); -- comment this line for a deadlock
  fork (\(_ : ()) -1-> write 5 w); 
  fork (\(_ : ()) -1-> write 6 w); 
  sleep 10000;
  read r
