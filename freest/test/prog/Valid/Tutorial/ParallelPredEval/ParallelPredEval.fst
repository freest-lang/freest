type PredEvalService : *C
type PredEvalService = *?PredEvalSession

type PredEvalSession : 1C
type PredEvalSession = !Int ; ?Bool ; Close

client : Int -> PredEvalService -> Bool
client n s =
    receive_ s |> send n |> receiveAndClose

gz : Dual PredEvalService -> ()
gz s =
    let(x, c) = receive (accept s) in sendAndWait (x > 0) c

_ =
    let (c, s) = channel @PredEvalService
        (j, a) = channel @ForkJoin in
    fork (\_ -> s |> gz                   ; join j) ;
    fork (\_ -> c |> client 5    |> print ; join j) ;
    fork (\_ -> c |> client (-1) |> print ; join j) ;
    fork (\_ -> s |> gz                   ; join j) ;
    -- fork (\_ -> s |> gz                   ; join j) ;
    fork (\_ -> c |> client 0    |> print ; join j) ;
    await 6 a