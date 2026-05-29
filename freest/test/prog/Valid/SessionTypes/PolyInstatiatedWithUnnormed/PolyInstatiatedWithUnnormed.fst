
module PolyInstantiatedWithUnnormed where

f : forall (a : 1S) -> !Char;a -> a
f @a c = send 'a' c

g : forall (a : 1S) -> ?Char;a -> a
g @a c = let (_, c) = receive c in c

type T : 1C
type T = !Int; T; ?Int

writer : Int -> T -> ()
writer i c =
  c |> send i |> writer (i + 1);
  ()

reader : Dual T -> ()
reader c =
  let (i, c) = receive c in
  print i;
  reader c

main : ()
main =
  let (w,r) = channel @(!Char; T) in
  fork (\(_ : ()) -1-> writer 0 (f w));
  reader (g r)

