module RecChan where

type Chan : 1C
type Chan = +{Done: Close, More: !Int;Chan}

fives : Int -> Chan -> ()
fives n c
  | n == 0    = select Done c |> close
  | otherwise = fives (n - 1) (c |> select More |> send 5)

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
  let _ = fork #1 (\(_ : ()) -1-> fives 32 w) in
  sumFives r
