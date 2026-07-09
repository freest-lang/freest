render : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
render (?type a . (?f ; ?x ; c)) =
  sendAndWait (f x) c

pairRenderer : !type a . !(a -1-> String) ; !a ; ?String ; Close -> String
pairRenderer c =
  c |> sendType @Char |> send showChar |> send 'F' |> receiveAndClose
  where
    showChar : Char -1-> String
    showChar c = "My favourite char: " ++ show c

_ =
  let x = forkWith render
  in print $ pairRenderer x
