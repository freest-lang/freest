module LinDataUnConsTwice where

-- In datatype constructor types, all arrows except the first 
-- after a linear field should be 1->, otherwise we can use 
-- the linear fields unrestrictedly.

type UnSend, UnRecv : 1T
data UnSend = UnSend (!Int; Close) () -- UnSend : !Int -> () 1-> UnSend
data UnRecv = UnRecv (?Int; Wait ) () -- UnRecv : ?Int -> () 1-> UnSend

unSend : Int -> (() 1-> UnSend) -> ()
unSend n us = case us () of
  UnSend s _ -> s |> send n |> close

unRecv : (() 1-> UnRecv) -> Int 
unRecv ur = case ur () of
  UnRecv r _ -> receiveAndWait r

main : Int
main = let (s, r) = channel @(!Int;Close) in 
       let us = UnSend s in -- us : () 1-> UnSend
       let ur = UnRecv r in -- ur : () 1-> UnRecv
       unSend 5 us;
       unSend 6 us; -- use twice (wrong: should not be in scope)
       unRecv ur;
       unRecv ur;
       unRecv ur    -- use thrice (wrong: should not be in scope)