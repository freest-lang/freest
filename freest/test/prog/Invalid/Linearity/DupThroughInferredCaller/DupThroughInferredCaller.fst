-- dup's kind is written; f's is inferred from the call to dup.
dup : forall (a : *T) -> a -> (a, a)
dup x = (x, x)

f : forall b -> b -> (b, b)
f y = dup y

main : ()
main = let (g, h) = f (\(x:Int) -1-> x) in print @Int (g 1 + h 2)
