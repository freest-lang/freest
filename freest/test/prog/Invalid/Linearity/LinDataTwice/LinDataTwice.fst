module LinDataTwice where

-- If a datatype contains a linear field, then it must be linear,
-- otherwise that field can be used unrestrictedly.

type UnSend, UnRecv : 1T
data UnSend = UnSend (!Int; Close)
data UnRecv = UnRecv (?Int; Wait )

unSend : Int -> UnSend -> ()
unSend n us = case us of 
  UnSend s -> s |> send n |> close

unRecv : UnRecv -> Int 
unRecv ur = case ur of
  UnRecv r -> receiveAndWait @Int r

main : Int
main = let (s, r) = channel @(!Int; Close) in 
       let us = UnSend s in -- us : UnSend (linear)
       let ur = UnRecv r in -- ur : UnSend (linear)
       unSend 5 us;
       unSend 6 us; -- use twice (wrong: should be out of scope)
       unRecv ur;
       unRecv ur;
       unRecv ur   -- use thrice (wrong: should be out of scope)