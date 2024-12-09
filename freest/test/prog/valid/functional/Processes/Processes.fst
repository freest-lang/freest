module Processes where

{-

TAPL, Page 271

Streams can be further generalized to a simple form of
processes—functions that accept a number and return a number and a new
process.

-}

type Process : *T
type Process = Int -> (Int, Process)

-- Here is a process that, at each step, returns the sum of all the
-- numbers it has been given so far:

sum : Int -> Process
sum acc n = let newAcc = acc + n in (newAcc, sum newAcc)

-- Interacting with processes

curr : Process -> Int
curr p = fst  @Int @Process (p 0)

send' : Int -> Process -> Process
send' n p = snd  @Int @Process (p n)

-- If we send the process p the numbers 5, 3, and 20, the number it
-- returns in response to the last interaction is 28.
main : Int
main = curr (send' 20 (send' 3 (send' 5 (sum 0))))
