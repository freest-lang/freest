module MovingAverage where

{- |
Module      :  MovingAverage
Description :  Calculates the moving average of a series of numbers
Copyright   :  (c) LASIGE and University of Lisbon, Portugal
Maintainer  :  Bernardo Almeida

Calculates the moving average of a sequence of values, with a window of 3.

Structure:
  - One thread sends values from 0 to 40, except whenever it would send a
    multiple of 10, it sends 100.

  - Another thread receives those values and computes the moving average of the
    current value with the previous two. Then, it sends the result to the main
    thread.

  - The main thread starts both threads, receives the values of the moving
    average and prints them.

-}

type FiniteOutStream, FiniteInStream : 1C
type FiniteOutStream = +{More: !Int;FiniteOutStream, Enough: Close}
type FiniteInStream = Dual FiniteOutStream

writeAll : Int -> FiniteOutStream -> ()
writeAll i c =
  if i <= 40 then
     select More c |>
     send (if mod i 10 == 0 then 100 else i) |>
     writeAll (i + 1)
  else c |> select Enough |> close

writeValues : !Int;!Int;FiniteOutStream;Close -> ()
writeValues c = c |> send 1 |> send 2 |> writeAll 3

average3 : Int -> Int -> Int -> Int
average3 x y z = (x + y + z) / 3

readAll : Int -> Int -> FiniteInStream -> FiniteOutStream -1-> ()
readAll x y from to =
  case from of
    &More from ->
      let (z, from) = receive from in
      select More to |>
      send (average3 x y z) |>
      readAll y z from
    &Enough from -> from |> wait ; to |> select Enough |> close

readValues : ?Int; ?Int; FiniteInStream -> FiniteOutStream -1-> ()
readValues from to =
  let (x, from) = receive from in
  let (y, from) = receive from in
  readAll x y from to

collectValues : FiniteInStream -> ()
collectValues c =
  case c of
    &More c ->
      let (v, c) = receive c in
      print v;
      collectValues c
    &Enough c -> c |> wait

main : ()
main =
  let r1 = forkWith writeValues in
  let r2 = forkWith (readValues r1) in
  collectValues r2
