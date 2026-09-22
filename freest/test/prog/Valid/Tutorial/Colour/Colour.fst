showColour : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showColour (&Green  Wait) = "Green"
showColour (&Yellow Wait) = "Yellow"
showColour (&Red    Wait) = "Red"

--If pattern matching is not an option, one can always try a `case` expression:
showColour' : &{Green: Wait, Yellow: Wait, Red: Wait} -> String
showColour' s = case s of
  &Green s  -> wait s ; "Green"
  &Yellow s -> wait s ; "Yellow"
  &Red s    -> wait s ; "Red"

-- The dual of the semaphore type, that is the type of the other channel endpoint, is `+{Green: Close, Yellow: Close, Red: Close}`. To consume one such channel endpoint, we take advantage of expression `select Green` (in this case):
selectGreen : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen c = c |> select Green |> close

-- Since `select Green` is an expression (`select` alone is not), one may as well write the above function using point-free programming, taking advantage of the function composition operator `.`:
selectGreen' : +{Green: Close, Yellow: Close, Red: Close} -> ()
selectGreen' = close . select Green

-- Putting the two functions together in a FreeST script we may write:
_ = forkWith selectGreen |> showColour |> putStrLn
