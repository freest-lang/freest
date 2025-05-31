module HelloWorldList where

type List : *T
data List = Nil | Cons Char List

type InCharStream, OutCharStream : 1S
type InCharStream = &{Done: Skip, More: ?Char;InCharStream}
type OutCharStream = Dual InCharStream

-- server : forall a . InCharStream;a -> (List, a)
server : forall (a : 1S). InCharStream;a -> (List, a)
server @a c =
  case c of
    &More c ->
      let (h, c) = receive @Char @(InCharStream;a) c in
      let (t, c) = server @a c in
      (Cons h t, c)
    &Done c ->
      (Nil, c)

client : forall (a : 1S). List -> OutCharStream;a -> a
client @a l c =
  case l of
    Nil ->
      select Done c
    Cons h t ->
--      client[a] l (send cons (select More c))
      let c = select More c in
      let c = send @Char h @(OutCharStream;a) c in
      let c3 = client @a t c in
      c3

hello, main : List

hello = Cons 'H' (Cons 'e' (Cons 'l' (Cons 'l' (Cons 'o' Nil))))

main = 
  let (c, s) = channel @(OutCharStream;Close) in
  let x = fork @() (\(_:()) 1-> close (client @Close hello c)) in
  let (res, c) = server @Wait s in
  (;) @() @List
    (wait c)
    res
