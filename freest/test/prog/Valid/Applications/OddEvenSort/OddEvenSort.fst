module OddEvenSort where

type Sorter : 1C
type Sorter = +{Done: Close, More: !Int ; ?Int; Sorter}

-- Exchange a value with a right node; return the min and the channel.
exchangeRight : Int -> Sorter -> (Int, Sorter)
exchangeRight x right =
  let (y, right) = receive (send x (select More right)) in
  (min x y, right)

-- first accepts the number of phases, the value in the node, the
-- channel to the right and the channel where to announce the result
-- once done. First is an odd process, hence it controls when sorting
-- is completed.
first : Int -> Int -> Sorter -> (!Int; Close) 1-> ()
first n x right collect' =
  if n == 0
  then select Done right |> close ; 
       send x collect' |> close
  else let (min, right) = exchangeRight x right in
       first (n - 1) min right collect'

-- Exchange a value with a right node; return the max and the channel.
exchangeLeft : Int -> (?Int; !Int; Dual Sorter) -> (Int, Dual Sorter)
exchangeLeft x left =
  let (y, left) = receive left in
  (max x y, send x left)

-- Consume the rest of a left channel once sorting in complete for an
-- odd process. The More branch is never exercised.
consume' : Dual Sorter -> ()
consume' c =
  case c of
    &Done c -> wait c
    &More c -> -- Should not happen
      let (_, c) = receive c in
      consume' (send (-99) c)

-- oddProcess accepts the number of phases, the value in the node, the
-- channel to the left, the channel to the right and the channel where
-- to announce the result once done. oddProcess is an odd process,
-- hence it controls when sorting is complete.

-- evenProcess accepts the number of phases, the value in the node,
-- the channel to the left, the channel to the right and the channel
-- where to announce the result once complete. evenProcess receives
-- from the left the announcement that sorting is completed (Done).

mutual
  oddProcess : Int -> Int -> Dual Sorter -> Sorter 1-> (!Int; Close) 1-> ()
  oddProcess n x left right collect' =
    if n == 0
    then select Done right |> close ; consume' left ; send x collect' |> close
    else let (min, right) = exchangeRight x right in
        evenProcess (n - 1) min left right collect'

  evenProcess : Int -> Int -> Dual Sorter -> Sorter 1-> (!Int; Close) 1-> ()
  evenProcess n x left right collect' =
    case left of
      &Done left -> wait left; select Done right |> close ; send x collect' |> close
      &More left -> let (max, left) = exchangeLeft x left in
                  oddProcess (n - 1) max left right collect'

-- last accepts the value in the node, the channel to the left and the
-- channel where to announce the result once done. last receives from
-- the left the announcement that sorting is completed (Done).
last : Int -> Dual Sorter -> (!Int; Close) 1-> ()
last x left collect' =
  case left of
    &Done left -> wait left; send x collect' |> close
    &More left -> let (max, left) = exchangeLeft x left in
                  last max left collect'

main : ()
main =
  -- number of inner processes
  let p = 5
  -- left-right communication channels
      (l1, r1) = channel @Sorter
      (l2, r2) = channel @Sorter
      (l3, r3) = channel @Sorter
      (l4, r4) = channel @Sorter
      (l5, r5) = channel @Sorter
      (l6, r6) = channel @Sorter
  -- collect' channels
      (cw1, cr1) = channel @(!Int; Close)
      (cw2, cr2) = channel @(!Int; Close)
      (cw3, cr3) = channel @(!Int; Close)
      (cw4, cr4) = channel @(!Int; Close)
      (cw5, cr5) = channel @(!Int; Close)
      (cw6, cr6) = channel @(!Int; Close)
      (cw7, cr7) = channel @(!Int; Close) in
  -- the various sorting nodes
  fork (\(_ : ()) 1-> first       (p / 2)     99    l1 cw1);
  fork (\(_ : ()) 1-> evenProcess (p / 2)     88 r1 l2 cw2);
  fork (\(_ : ()) 1-> oddProcess  (p / 2 - 1) 33 r2 l3 cw3);
  fork (\(_ : ()) 1-> evenProcess (p / 2)     11 r3 l4 cw4);
  fork (\(_ : ()) 1-> oddProcess  (p / 2 - 1) 55 r4 l5 cw5);
  fork (\(_ : ()) 1-> evenProcess (p / 2)     44 r5 l6 cw6);
  fork (\(_ : ()) 1-> last                    77 r6    cw7);
  -- collect' and print results
  print (receiveAndWait cr1);
  print (receiveAndWait cr2);
  print (receiveAndWait cr3);
  print (receiveAndWait cr4);
  print (receiveAndWait cr5);
  print (receiveAndWait cr6);
  print (receiveAndWait cr7)
