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

-- | Collect the values read by the two reader threads (on channel c) and the
-- value read by main (z), and check that they make sense.
test : *?Int -> Int -> ()
test c z =
  if check (receive_ c) (receive_ c) z
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | Each value read is one of those written: 4, 5 or 6
    valid : Int -> Bool
    valid n = n == 4 || n == 5 || n == 6
    -- | Reads are destructive: each value written is read exactly once
    check : Int -> Int -> Int -> Bool
    check x y z =
      valid x && valid y && valid z && x /= y && y /= z && x /= z

-- Readers report the values read on a shared channel; writers signal
-- completion on a fork-join channel.
main : ()
main =
  let (writeEnd, readEnd)     = channel @IntCell
      (joinEnd, awaitEnd)     = channel @ForkJoin
      (collectEnd, reportEnd) = channel @(*?Int) in
  fork (\_ -1-> send_ (read readEnd) reportEnd ; ());
  fork (\_ -1-> send_ (read readEnd) reportEnd ; ());
  fork (\_ -1-> write 4 writeEnd ; join joinEnd); -- comment this line for a deadlock
  fork (\_ -1-> write 5 writeEnd ; join joinEnd);
  fork (\_ -1-> write 6 writeEnd ; join joinEnd);
  await 3 awaitEnd;
  test collectEnd (read readEnd)
