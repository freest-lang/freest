getLine' :  () -> String
getLine' _ = 
  let (x, c) = stdin |> receive_ |> select GetLine |> receive in
  hCloseIn c; 
  x

_ =
  putStrLn $ getLine' ()