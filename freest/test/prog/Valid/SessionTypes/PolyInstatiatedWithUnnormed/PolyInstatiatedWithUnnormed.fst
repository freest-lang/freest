
module PolyInstantiatedWithUnnormed where

f : !Char;a -> a
f c = let c = send 'a' c in c

g : ?Char;a -> a
g c = let (_,c) = receive c in c


writer : Int -> T -> ()
writer i c =
  let _ = writer (i + 1) (send i c)
  in ()

reader : Dual T -> ()
reader c =
  let (i, c) = receive c in
  print @Int i;
  reader c

type T : 1S
type T = !Int;T;?Int

main : ()
main =
  let (w,r) = channel @(!Char;T) in
  fork (\_:() 1-> f @T w |> writer 0) ;
  g @(Dual T) r |> reader

