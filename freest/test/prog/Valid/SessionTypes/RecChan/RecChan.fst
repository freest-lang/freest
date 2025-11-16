module RecChan where

type Chan : 1C
type Chan = +{Done: Close, More: !Int;Chan}

fives : Int -> Chan -> ()
fives n c =
  if n == 0
  then select Done c |> close
  else fives (n-1) (select More c |> send 5)

sumFives : Dual Chan -> Int
sumFives c =
  case c of
    &Done c -> wait c; 0
    &More c ->
     let (n, c) = receive c in
     n + sumFives c

main : Int
main =
  let (w, r) = channel @Chan in
  let _ = fork @() (\(_ : ()) 1-> fives 32 w) in
  sumFives r
