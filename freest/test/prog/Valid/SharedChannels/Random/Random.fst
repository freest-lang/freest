type IntStream : *C
type IntStream = *!Int

type BitStream, Random : *C
type BitStream = IntStream
type Random    = Dual IntStream

-- Args -> *!SendType
genericUnSender : forall a -> a -> *!a -> ()
genericUnSender @a x chan =
    chan |> send_ x |> genericUnSender x

receiveBits : Int -> Dual BitStream -> Int
receiveBits nBits bitS
    | nBits < 0 = 0
    | otherwise = receive_ bitS + (receiveBits (nBits-1) bitS) * 2

initRandom : Random
initRandom =
    -- init bit sending 
    let (bitSend, bitRecv) = channel @BitStream in
    -- init bit sending threads
    fork (\_ -1-> genericUnSender 0 bitSend);
    fork (\_ -1-> genericUnSender 1 bitSend);
    -- init server/client endpoint
    let (client, server) = channel @Random in
    -- init random server
    fork (\_ -1-> genericUnSender (receiveBits 4 bitRecv) server);
    -- return client endpoint
    client

-- | Collect a random number (on channel r) and check that it makes sense.
test : Random -> ()
test r =
  if check (receive_ r)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | 'receiveBits 4' reads five bits (for nBits = 4, 3, 2, 1, 0), hence a
    -- number between 0 and 31
    check : Int -> Bool
    check n = 0 <= n && n <= 31

main : ()
main = test initRandom
