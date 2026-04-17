module HelloWorldList where

type List : *T
data List = Nil | Cons Char List

type InCharStream, OutCharStream : 1S
type InCharStream = &{Done: Skip, More: ?Char;InCharStream}
type OutCharStream = Dual InCharStream

-- server : forall a . InCharStream;a -> (List, a)
server : forall (a : 1S). (InCharStream; a) -> (List, a)
server @a c =
  case c of
    &More c ->
      let (h, c) = receive c in
      let (t, c) = server c in
      (Cons h t, c)
    &Done c ->
      (Nil, c)

client : forall (a : 1S). List -> (OutCharStream; a) -> a
client @a l c =
  case l of
    Nil ->
      select Done c
    Cons h t ->
      c |> select More |> send h |> client t

hello, main : List

hello = Cons 'H' (Cons 'e' (Cons 'l' (Cons 'l' (Cons 'o' Nil))))

main = 
  let (c, s) = channel @(OutCharStream; Close) in
  fork (\(_ : ()) 1-> c |> client hello |> close);
  let (res, c) = server s in
  wait c;
  res
