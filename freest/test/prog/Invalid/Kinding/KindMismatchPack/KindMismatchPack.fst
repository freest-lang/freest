module KindMismatchPack where

main : ()
main = (@(Int 1-> Int), \(x : Int) 1-> x) 
     : exists (a : *T). a 