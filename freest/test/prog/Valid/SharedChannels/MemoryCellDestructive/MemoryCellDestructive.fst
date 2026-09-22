-- A memory cell with destructive reads. The successive values of the cell are
-- messages in transit. A read operation reads one such message, thus "clearing"
-- the contents of the cell. In this way reading from a memory cell may be a
-- blocking operation. Works only with no less writes than reads, properly
-- interleaved.
type IntCell : *C
type IntCell = *!Int

write: Int -> IntCell -1-> IntCell
write i c = send_ i c

read: Dual IntCell -> Int
read = receive_

main: Int
main =
  let (w, r) = channel @IntCell in
  let (f, j) = channel @ForkJoin in
  fork (\_ -1-> read r    ; join f);
  fork (\_ -1-> read r    ; join f);
  fork (\_ -1-> write 4 w ; join f); -- comment this line for a deadlock
  fork (\_ -1-> write 5 w ; join f);
  fork (\_ -1-> write 6 w ; join f);
  await 5 j;
  read r
