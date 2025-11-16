module DualArrow where

type RcvInt : 1S
type RcvInt = ?Int

type Arrow : *T
type Arrow = Int -> Dual RcvInt -> Int

sendInt : Arrow
sendInt i c = send i c; 0 -- zero just for test purposes

rcvInt : Dual Arrow
rcvInt i c = let (j, c) = receive c in j
