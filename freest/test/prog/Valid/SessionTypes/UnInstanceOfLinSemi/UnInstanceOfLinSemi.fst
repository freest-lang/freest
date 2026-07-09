id' : forall a b -> a; b -> a; b
id' @a @b c = c

main : ()
main = 
  let (c, _) = channel @*!Int
  in id' @Skip @*!Int c; 
     ()
