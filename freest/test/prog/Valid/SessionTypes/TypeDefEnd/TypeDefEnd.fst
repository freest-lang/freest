module TypeDefEnd where

type T : 1S
type T = Wait

main : ()
main = let (r,w) = channel @T in fork (\_:()1-> wait r); close w
