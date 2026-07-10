render : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
render (?type a . ?f ; ?x ; c) =
  sendAndWait (f x) c

-- Same as `render`, but using the `receiveType` primitive instead of
-- pattern-matching the session on the left-hand side.
render' : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
render' c =
  let (@a, c) = receiveType c in
  let (f, c)  = receive c in
  let (x, c)  = receive c in
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
  forkWith render' |>
  charRenderer

_ = print (charRenderer (forkWith render))

_ =
  forkWith render |>
  charRenderer |>
  print
