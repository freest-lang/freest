module Random where

type IntStream : *C
type IntStream = *!Int

type BitStream, Random : *C
type BitStream = IntStream
type Random    = Dual IntStream

-- Args -> *!SendType
genericUnSender : forall (a : *T). a -> *!a -> ()
genericUnSender @a x chan =
    genericUnSender @a x $ send x chan

receiveBits : Int -> Dual BitStream -> Int
receiveBits nBits bitS = 
    if nBits < 0
    then 0
    else
        let (i, bitS) = receive bitS in
        i + (receiveBits (nBits-1) bitS) * 2

initRandom : Random
initRandom =
    -- init bit sending 
    let (bitSend, bitRecv) = channel @BitStream in
    -- init bit sending threads
    fork (\(_ : ()) 1-> genericUnSender @Int 0 bitSend);
    fork (\(_ : ()) 1-> genericUnSender @Int 1 bitSend);
    -- init server/client endpoint
    let (client, server) = channel @Random in
    -- init random server
    fork (\(_ : ()) 1-> genericUnSender @Int (receiveBits 4 bitRecv) server);
    -- return client endpoint
    client

main : Int
main =
    let rand = initRandom in
    let (i, _) = receive rand in
	i