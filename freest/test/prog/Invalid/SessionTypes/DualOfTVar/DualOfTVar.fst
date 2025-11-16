module DualOfTVar where

mynew : forall (a : 1C). (a, Dual a)
mynew @a = channel @a

run : forall (a : 1C). (a -> ()) 1-> (Dual a -> ()) 1-> ()
run @a f g = let (x, y) = mynew @a in fork (\(_ : ()) 1-> f x); g y

write : !Int -> ()
write c = send 5 c; ()

read : ?Int -> ()
read c = receive c; ()

main : ()
main = run @(!Int) write read
