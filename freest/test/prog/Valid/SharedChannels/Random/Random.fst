module Random where

type IntStream : *C
type IntStream = *!Int

type BitStream, Random : *C
type BitStream = IntStream
type Random    = Dual IntStream

-- Args -> *!SendType
genericUnSender : forall (a : *T) -> a -> *!a -> ()
genericUnSender @a x chan =
    send_ x chan; genericUnSender x chan

receiveBits : Int -> Dual BitStream -> Int
receiveBits nBits bitS = 
    if nBits < 0
    then 0
    else receive_ bitS + (receiveBits (nBits-1) bitS) * 2

initRandom : Random
initRandom =
    -- init bit sending 
    let (bitSend, bitRecv) = channel @BitStream in
    -- init bit sending threads
    fork #1 (\(_ : ()) -1-> genericUnSender 0 bitSend);
    fork #1 (\(_ : ()) -1-> genericUnSender 1 bitSend);
    -- init server/client endpoint
    let (client, server) = channel @Random in
    -- init random server
    fork #1 (\(_ : ()) -1-> genericUnSender (receiveBits 4 bitRecv) server);
    -- return client endpoint
    client

main : Int
main = receive_ initRandom