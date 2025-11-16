module SharedMathServer where

type MathServer : *C
type MathServer  = *?MathService

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
    runMathService (accept @MathService ch) ;
    runMathServer (n - 1) ch

client1 : MathServer -> ()
client1 ch =
  let c = receive_ @MathService ch in
  let (n, c) = c |> select Plus |> send 1 |> send 2 |> receive in
  let (m, c) = c |> select Neg |> send n |> receive in
  print @Int m;
  c |> select Done |> close

client2 : MathServer -> ()
client2 ch =
  let c = receive_ @MathService ch in
  let (b, c) = c |> select Gt |> send 2 |> send 1 |> receive in
  print @Bool b;
  c|> select Done |> close

main : ()
main =
  let (c, s) = channel @MathServer in
  fork (\(_ : ()) 1-> client1 c);
  fork (\(_ : ()) 1-> client2 c);
  runMathServer 2 s
