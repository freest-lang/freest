module SumSendPairError where

-- TEST ERROR MESSAGES

type Value : *T
type Value = Int

type Triple : 1T
type Triple = (!Int;Close, (Value, Value))

type Pair : 1T
type Pair = (!Int;Close, Value)

pairToValue : Pair -> Value
pairToValue p =
  let (x, y) = p in x + y

sendValue : Triple -> ()
sendValue t =
  let (c, pair) = t in
  send c (pairToValue pair) |> close
  
rcvValue : ?Int -> Value
rcvValue c = let (v, c) = receive c in v
  
main : Value
main =
  let (x, y) = channel @(!Int; Close) () in   
  let aTriple = (x, (2, 3)) in
  fork @() (\(_ : ()) 1-> sendValue aTriple);
  let (x, c) = receive y in wait c; x     
