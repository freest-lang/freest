module UnInstanceOfLinSemi where

id' : forall (a : 1S) (b : 1S) -> a; b -> a; b
id' @a @b c = c

main : ()
main = 
  let (c, _) = channel @*!Int
  in id' @Skip @*!Int c; 
     ()
