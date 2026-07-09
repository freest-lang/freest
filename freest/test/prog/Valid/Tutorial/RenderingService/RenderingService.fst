render : ?type a . ?(a -1-> String) ; ?a ; !String ; Wait -> ()
render (?type a . (?f ; ?x ; c)) =
  sendAndWait (f x) c

_ = print (1, True)