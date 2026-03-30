module LinComponentInMatch where

type Server : 1C
type Server = &{A: !Int}; Wait

server : Server -> () 1-> ()
server s _ =
  case s of &A s -> () -- here

main : Int
main = let (s, c) = channel @Server in
       fork (server s);
       c |> select A |> receiveAndClose @Int
