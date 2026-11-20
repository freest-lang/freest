-- Fork three threads and wait for all of them to finish. Each thread sends its
-- character back to the main thread, which checks them (deterministic output,
-- for testing purposes).

-- | Collect the three characters (on channel c) and check that they make sense.
test : *?Char -> ()
test c =
  if check (receive_ c) (receive_ c) (receive_ c)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | Character equality (in the Prelude, (==) is on Int only)
    eq : Char -> Char -> Bool
    eq x y = ord x == ord y
    -- | Each character is one of 'A', 'B' or 'C'
    valid : Char -> Bool
    valid x = eq x 'A' || eq x 'B' || eq x 'C'
    -- | The three characters are 'A', 'B' and 'C', in any order
    check : Char -> Char -> Char -> Bool
    check x y z =
      valid x && valid y && valid z &&
      not (eq x y) && not (eq y z) && not (eq x z)

-- Threads report their characters on a shared channel and signal completion on
-- a fork-join channel.
main : ()
main =
  let (joinEnd, awaitEnd)     = channel @ForkJoin
      (collectEnd, reportEnd) = channel @(*?Char) in
  fork (\_ -> send_ 'A' reportEnd ; join joinEnd) ;
  fork (\_ -> send_ 'B' reportEnd ; join joinEnd) ;
  fork (\_ -> send_ 'C' reportEnd ; join joinEnd) ;
  await 3 awaitEnd ;
  test collectEnd
