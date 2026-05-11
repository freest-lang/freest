{-|
 The (regular) protocol for an arithmetic stream

type Stream = +{
	Add: Stream,
	Mult: Stream,
	Const: !Int. Stream,
	EOS: ?Int. end
}
-}

module ArithExprServerRegular where

type StreamClient, StreamServer : 1C
type StreamClient = +{ Add  : StreamClient
                     , Mult : StreamClient
                     , Const: !Int; StreamClient
                     , EOS  : ?Int; Wait 
                     }
type StreamServer = Dual StreamClient

-- A sample client: (5*4)+(2*3)
client : StreamClient -> Int
client c = c |> select Const
             |> send 5
             |> select Const
             |> send 4
             |> select Mult
             |> select Const
             |> send 2
             |> select Const
             |> send 3
             |> select Mult
             |> select Add
             |> select EOS
             |> receiveAndWait

{-|
  An easy consumer: counts the number of nodes in the stream.  Copes
  with any stream, independent of the fact that it may or may not
  represent a well formed arithmetic expression.
-}
size : StreamServer -> Int -1-> ()
size s n =
  case s of
    &Add s   -> size s (n + 1)
    &Mult s  -> size s (n + 1)
    &Const s -> let (_, s) = receive s in size s (n + 1)
    &EOS s   -> s |> send n |> close

-- A sample interaction: counting the number of nodes in a stream;
-- expect 7 on the console.
main : Int
main =
  let (c, s) = channel @StreamClient in
  fork #1 (\(_:()) -1-> size s 0);
  client c
