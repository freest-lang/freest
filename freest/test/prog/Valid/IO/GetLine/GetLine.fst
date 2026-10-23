getLine' :  () -> String
getLine' _ = 
  let (x, c) = stdin |> request |> select GetLine |> receive in
  hCloseIn c; 
  x

_ =
  putStrLn $ getLine' ()