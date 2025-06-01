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

type StreamClient, StreamServer : 1S

type StreamClient = +{ Add  : StreamClient
                     , Mult : StreamClient
                     , Const: !Int; StreamClient
                     , EOS  : ?Int; Wait 
                     }
type StreamServer = Dual StreamClient

-- A sample client: (5*4)+(2*3)
client : StreamClient -> Int
client c =
  receiveAndWait @Int
    (select EOS
      (select Add 
        (select Mult 
          (send @Int 3 @StreamClient
            (select Const 
              (send @Int 2 @StreamClient
                (select Const 
                  (select Mult 
                    (send @Int 4 @StreamClient
                      (select Const 
                        (send @Int 5 @StreamClient
                          (select Const c))))))))))))

{-|
  An easy consumer: counts the number of nodes in the stream.  Copes
  with any stream, independent of the fact that it may or may not
  represent a well formed arithmetic expression.
-}
size : StreamServer -> Int 1-> ()
size s n =
  case s of
    &Add s   -> size s (n + 1)
    &Mult s  -> size s (n + 1)
    &Const s -> let (_, s) = receive @Int @StreamServer s in size s (n + 1)
    &EOS s   -> close (send @Int n @Close s)

-- A sample interaction: counting the number of nodes in a stream;
-- expect 7 on the console.
main : Int
main =
  let (c, s) = channel @StreamClient in
  let _ = fork @() (\(_:()) 1-> size s 0) in
  client c
