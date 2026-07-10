render : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
render (?type a . ?f ; ?x ; c) =
  sendAndWait (f x) c

charRenderer : !type a . !(a -1-> String) ; !a ; ?String ; Close -> String
charRenderer c =
  c |> sendType @Char |> send showChar |> send 'F' |> receiveAndClose
  where
    showChar : Char -1-> String
    showChar c = "My favourite char is " ++ show c

pairRenderer : !type a . !(a -1-> String) ; !a ; ?String ; Close -> String
pairRenderer c =
  c |> sendType @(String, Float) |> send showPair |> send ("FreeST", 5.0) |> receiveAndClose
  where
    showPair : (String, Float) -1-> String
    showPair (x, y) = x ++ " " ++ show y

_ = print $
  forkWith render |>
  charRenderer

_ = print $ 
  forkWith render |>
  pairRenderer
