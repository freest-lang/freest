_ =
  putStr "What is your name? ";
  let name = getLine () in
  putStrLn ("Hello, " ++ name ++ "!")
