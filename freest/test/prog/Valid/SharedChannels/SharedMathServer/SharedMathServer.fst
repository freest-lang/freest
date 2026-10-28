type MathServer : *C
type MathServer  = *!(Dual MathService)

type MathService : 1C
type MathService = +{ Plus: !Int; !Int; ?Int; MathService
                    , Gt  : !Int; !Int; ?Bool; MathService
                    , Neg : !Int; ?Int; MathService
                    , Done: Close 
                    }

runMathService : Dual MathService -> ()
runMathService (&Plus s) =
  let (n1, s) = receive s in
  let (n2, s) = receive s in
  runMathService $ send (n1 + n2) s
runMathService (&Gt s) =
  let (n1, s) = receive s in
  let (n2, s) = receive s in
  runMathService $ send (n1 > n2) s
runMathService (&Neg s) =
  let (n1, s) = receive s in
  runMathService $ send (-n1) s
runMathService (&Done s) =
  wait s

-- Serve one client at a time. Try variant where runMathService runs on a
-- separate thread, for better throughput.
-- n is the number of expected clients 
runMathServer : Int -> Dual MathServer -> ()
runMathServer n ch =
  if n == 0 then ()
  else
    runMathService (accept ch) ;
    runMathServer (n - 1) ch

-- | Compute -(1 + 2)
client1 : MathServer -> Int
client1 ch =
  let c = request ch in
  let (n, c) = c |> select Plus |> send 1 |> send 2 |> receive in
  let (m, c) = c |> select Neg  |> send n |> receive in
  c |> select Done |> close ;
  m

-- | Compute 2 > 1
client2 : MathServer -> Bool
client2 ch =
  let c = request ch in
  let (b, c) = c |> select Gt |> send 2 |> send 1 |> receive in
  c |> select Done |> close ;
  b

-- | Collect the answers of the two clients (on channels ci and cb) and check
-- that they make sense.
test : *?Int -> *?Bool -> ()
test ci cb =
  if check (receive_ ci) (receive_ cb)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | -(1 + 2) is -3 and 2 > 1 is True
    check : Int -> Bool -> Bool
    check m b = m == -3 && b

-- Clients report their answers on shared channels, one per type of answer
-- (receiving both answers tells main that the clients are done).
main : ()
main =
  let (clientEnd, serverEnd)          = channel @MathServer
      (collectIntEnd, reportIntEnd)   = channel @(*?Int)
      (collectBoolEnd, reportBoolEnd) = channel @(*?Bool) in
  fork (\_ -> send_ (client1 clientEnd) reportIntEnd  ; ()) ;
  fork (\_ -> send_ (client2 clientEnd) reportBoolEnd ; ()) ;
  runMathServer 2 serverEnd ;
  test collectIntEnd collectBoolEnd
