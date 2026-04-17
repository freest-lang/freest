module Repeat where

-- TODO: this test should be revised

-- 1 _ Stream
type Stream : 1T -> 1C
type Stream (a : 1T) = !a; Stream a

-- An arbitrary Stream consumer
consumeStream : forall (a : 1T). -- ∀ α .
  (Stream a -> Stream a) -> -- A function that consumes the head of a stream
  Stream a ->                    -- The stream
  ()
consumeStream @a f c = consumeStream @a f (f c)

-- Write on an int on a channel; return the continuation channel
writeInt : forall (b : 1S). (!Int; b) -> b
writeInt @b c = send 7 c

writeIntStream : Stream Int -> ()
writeIntStream = consumeStream @Int (writeInt @(Stream Int))

-- Read from an int stream
readInt' : forall (b : 1S). ?Int; b -> b
readInt' @b c = let (v, c) = receive c in print v; c

readIntStream : Dual (Stream Int) -> ()
readIntStream = consumeStream @Int (readInt' @(Dual (Stream Int)))

-- Run an int stream
mainIntStream : ()
mainIntStream =
  let (w, r) = channel @(Stream Int) in
  fork (\(_ : ()) 1-> writeIntStream w);
  readIntStream r

-- 2 _ Stream of out-char-in-bool values
type OutCharInBoolStream : 1C
type OutCharInBoolStream = !Char; ?Bool; OutCharInBoolStream

-- Write and read on an out-char-in-bool stream; return the continuation channel
writeCharReadBool : forall (b : 1S). !Char; ?Bool; b -> b
writeCharReadBool @b c =
  let (v, c) = receive (send 'z' c) in printBool v; c

writeCharReadBoolStream : OutCharInBoolStream -> ()
writeCharReadBoolStream =
  consumeStream @(!Char; ?Bool) writeCharReadBool @OutCharInBoolStream

writeIntStream1 : Stream Int -> ()
writeIntStream1 = produceStream  @Int (\(c : Stream Int) -> send 7 c)

-- Run an out-char-in-bool stream
mainCharBoolStream : ()
mainCharBoolStream =
  let (w, r) = channel @OutCharInBoolStream in
  fork (\(_ : ()) 1-> writeCharReadBoolStream w);
  readCharWriteBoolStream r

main : ()
main =
  let (w, r) = channel @(Stream Int) in
  fork @() (\(_ : ()) 1-> writeIntStream1 w);
  readIntStream r
