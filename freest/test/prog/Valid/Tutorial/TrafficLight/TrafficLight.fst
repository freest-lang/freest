-- With pattern-matching: preferred
showTrafficLight : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showTrafficLight (&Green  Wait) = "Green"
showTrafficLight (&Yellow Wait) = "Yellow"
showTrafficLight (&Red    Wait) = "Red"

-- With a case expression
showTrafficLight' : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showTrafficLight' s = case s of
  &Green s  -> wait s ; "Green"
  &Yellow s -> wait s ; "Yellow"
  &Red s    -> wait s ; "Red"

selectGreen : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen c = c |> select Green |> close

-- Point free programming
selectGreen' : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen' = close . select Green

_ = forkWith selectGreen |> showTrafficLight |> putStrLn
