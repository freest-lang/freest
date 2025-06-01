
module PolyInstantiatedWithUnnormed where

f : forall (a : 1S). !Char;a -> a
f @a c = let c = send @Char 'a' @a c in c

g : forall (a : 1S). ?Char;a -> a
g @a c = let (_,c) = receive @Char @a c in c

type T : 1S
type T = !Int;T;?Int

writer : Int -> T -> ()
writer i c =
  let _ = writer (i + 1) (send @Int i @(T;?Int) c)
  in ()

reader : Dual T -> ()
reader c =
  let (i, c) = receive @Int @((Dual T); !Int) c in
  (;) @() @() 
    (print @Int i)
    (reader c)

main : ()
main =
  let (w,r) = channel @(!Char;T) in
  (;) @() @() 
    (fork @() (\(_:()) 1-> writer 0 (f @T w)))
    (reader (g @(Dual T) r))

