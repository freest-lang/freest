module Triple where

type Value = Int
type Triple = (Value, (Value, Value))
type Pair = (Value, Value)

-- type Arrow = Int -> dualof RcvInt -> Int

tripleToPair : Triple -> Pair
tripleToPair t =
  let (x, y) = t in
  let (k, z) = y in (x, k + z)

pairToValue : Pair -> Value
pairToValue p =
  let (x, y) = p in x+y

main : Value
main =
  let aTriple = (1, (2, 3)) in
  pairToValue (tripleToPair aTriple)
  
