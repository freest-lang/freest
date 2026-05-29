module KindMismatchUnpack where

main : ()
main =
  let (@(a : *T), _) = (@(Int 1-> Int), \(x : Int) 1-> x)
                     : exists (a : 1T). a
  in ()