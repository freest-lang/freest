module DataReuseBoundVar where

type T : *T
data T = C Int

main : Int
main = 
  (case C 5 of C x -> 5); x
