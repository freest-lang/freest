module Triple where

type Value = Int
type Triple = (Value, Value, Value)
type Pair = (Value, Value)

-- type Arrow = Int -> Dual RcvInt -> Int

tripleToPair : Triple -> Pair
tripleToPair t =
  let (x, y, z) = t in
  (x, y + z)

pairToValue : Pair -> Value
pairToValue p =
  let (x, y) = p in x + y

main : ()
main =
  let aTriple = (1, 2, 3) in
  print (pairToValue (tripleToPair aTriple))
