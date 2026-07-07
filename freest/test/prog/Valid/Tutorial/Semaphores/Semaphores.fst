showSemaphore : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showSemaphore (&Green s) = wait s ; "Green"
showSemaphore (&Yellow s) = wait s ; "Yellow"
showSemaphore (&Red s) = wait s ; "Red"

showSemaphore' : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showSemaphore' s = case s of
  &Green s  -> wait s ; "Green"
  &Yellow s -> wait s ; "Yellow"
  &Red s    -> wait s ; "Red"

selectGreen : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen c = c |> select Green |> close

selectGreen' : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen' = close . select Green

_ =
  let x = forkWith selectGreen
  in print $ showSemaphore x
