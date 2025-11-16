{-

TAPL, page 270

"A more useful variant of the Hungry type above is the type Stream of functions that can consume an arbitrary number of unit values, each time returning a pair of a number and a new stream."
-}

module Streams where

-- A more useful variant of the Hungry type above is the type Stream
-- of functions that can consume an arbitrary number of unit values,
-- each time returning a pair of a number and a new stream.

type Stream : *T
type Stream = () -> (Int, Stream) 

{- Alternatives:
type Stream = rec x:TU. () -> (Int, x) 
type Stream = rec x. () -> (Int, x) 
-}

-- We can define two “destructors” for streams; if s is a stream, then
-- hd s is the first number it returns when we pass it unit.

hd : Stream -> Int
hd s = fst  @Int @Stream (s ())

-- Similarly, tl s is the new stream that we obtain when we pass unit to s.

tl : Stream -> Stream
tl s = snd  @Int @Stream (s ())

-- Construct a stream

upFrom : Int -> Stream
upFrom n = (\ (_ : ()) -> (n, upFrom (n + 1)))

-- The third element in the upFrom 0 stream

main : Int
main = hd (tl (tl (tl (upFrom 0))))
