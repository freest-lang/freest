module Triple where

type Value : *T
type Value = Int
type Triple : *T
type Triple = (Value, Value, Value)
type Pair : *T
type Pair = (Value, Value)

-- type Arrow = Int -> Dual RcvInt -> Int

tripleToPair : Triple -> Pair
tripleToPair t =
  let (x, y, z) = t in
  (x, y + z)

pairToValue : Pair -> Value
pairToValue p =
  let (x, y) = p in x + y

main : Value
main =
  let aTriple = (1, 2, 3) in
  pairToValue (tripleToPair aTriple)
  
