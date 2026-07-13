renderer : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
renderer (?type a . ?f ; ?x ; c) =
  sendAndWait (f x) c









-- Same as `render`, but using the `receiveType` primitive instead of
-- pattern-matching the session on the left-hand side.
renderer' : ?type (a:*T) . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
renderer' c =
  let (@a, c) = receiveType c in
  let (f, c)  = receive c in
  let (x, c)  = receive c in
  sendAndWait (f x) c




charRendererClient : !type a . !(a -1-> String) ; !a ; ?String ; Close -> String
charRendererClient c =
  c |> sendType @Char |> send showChar |> send 'F' |> receiveAndClose
  where
    showChar : Char -1-> String
    showChar c = "My favourite char is " ++ show c

pairRendererClient : !type a . !(a -1-> String) ; !a ; ?String ; Close -> String
pairRendererClient c =
  c |> sendType @(String, Float) |> send showPair |> send ("FreeST", 5.0) |> receiveAndClose
  where
    showPair : (String, Float) -1-> String
    showPair (x, y) = x ++ " " ++ show y



_ = forkWith renderer |> charRendererClient |> print

-- _ = print (charRendererClient (forkWith renderer))

-- _ = forkWith renderer |> pairRendererClient |> print
