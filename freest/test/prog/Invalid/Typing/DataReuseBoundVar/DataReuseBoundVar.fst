module DataReuseBoundVar where

data T = C Int

main : Int
main = 
  let _ = case C 5 of C x -> 5
  in x
