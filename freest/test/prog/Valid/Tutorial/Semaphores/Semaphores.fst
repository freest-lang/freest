-- With pattern-matching: preferred
showSemaphore : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showSemaphore (&Green  Wait) = "Green"
showSemaphore (&Yellow Wait) = "Yellow"
showSemaphore (&Red    Wait) = "Red"









-- With a case expression
showSemaphore' : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showSemaphore' s = case s of
  &Green s  -> wait s ; "Green"
  &Yellow s -> wait s ; "Yellow"
  &Red s    -> wait s ; "Red"



selectGreen : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen c = c |> select Green |> close

-- Point free programming
selectGreen' : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen' = close . select Green

_ = forkWith selectGreen |> showSemaphore |> putStrLn
