module InvalidExtractBasic where

type Tree : *T
data Tree = Leaf | Node Int Tree Tree

-- invalid extract pair: Expecting a pair type; found Bool
fun : (!Int; Close) -> Tree -> Bool
fun c t = send t c |> close; True
