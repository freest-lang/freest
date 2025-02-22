module HelloWorldList where

type List : *T
data List = Nil | Cons Char List

type InCharStream, OutCharStream : 1S
type InCharStream = &{Done: Skip, More: ?Char;InCharStream}
type OutCharStream = Dual InCharStream

-- server : forall a . InCharStream;a -> (List, a)
server : InCharStream;a -> (List, a)
server c =
  case c of
    &More c ->
      let (h, c) = receive c in
      let (t, c) = server @a c in
      (Cons h t, c)
    &Done c ->
      (Nil, c)

client : List -> OutCharStream;a -> a
client l c =
  case l of
    Nil ->
      select Done c
    Cons h t ->
--      client[a] l (send cons (select More c))
      let c = select More c in
      let c = send h c in
      let c3 = client @a t c in
      c3

hello, main : List

hello = Cons 'H' (Cons 'e' (Cons 'l' (Cons 'l' (Cons 'o' Nil))))

main = 
  let (c, s) = channel @(OutCharStream;Close) in
  let x = fork @() (\_:()1-> client @Close hello c |> close) in
  let (res, c) = server @Wait s in
  wait c;
  res
