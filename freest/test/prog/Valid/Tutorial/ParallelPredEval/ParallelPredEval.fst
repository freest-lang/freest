type PredEvalService : *C
type PredEvalService = *!(Dual PredEvalSession)

type PredEvalSession : 1C
type PredEvalSession = !Int ; ?Bool ; Close

client : Int -> PredEvalService -> Bool
client n s =
    request s |> send n |> receiveAndClose

gz : Dual PredEvalService -> ()
gz s =
    let (x, c) = receive (accept s) in sendAndWait (x > 0) c

-- | Collect the three answers (on channel c) and check that they make sense.
test : *?Bool -> ()
test c =
  if check (receive_ c) (receive_ c) (receive_ c)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | One for True, zero for False
    count : Bool -> Int
    count b = if b then 1 else 0
    -- | Only one of 5, -1 and 0 is greater than zero: expect one True and two
    -- False, in any order
    check : Bool -> Bool -> Bool -> Bool
    check x y z = count x + count y + count z == 1

-- Clients report their answers on a shared channel (receiving three answers
-- tells main that the clients are done); servers signal completion on a
-- fork-join channel.
main : ()
main =
    let (clientEnd, serverEnd)  = channel @PredEvalService
        (joinEnd, awaitEnd)     = channel @ForkJoin
        (collectEnd, reportEnd) = channel @(*?Bool) in
    fork (\_ -> serverEnd |> gz                            ; join joinEnd) ;
    fork (\_ -> send_ (clientEnd |> client 5)    reportEnd ; ()) ;
    fork (\_ -> send_ (clientEnd |> client (-1)) reportEnd ; ()) ;
    fork (\_ -> serverEnd |> gz                            ; join joinEnd) ;
    fork (\_ -> serverEnd |> gz                            ; join joinEnd) ;
    fork (\_ -> send_ (clientEnd |> client 0)    reportEnd ; ()) ;
    await 3 awaitEnd ;
    test collectEnd
