-- The control for DupInferredBinderKind.
dup : forall (a : *T) -> a -> (a, a)
dup x = (x, x)

main : ()
main = let (f, g) = dup (\(x:Int) -1-> x) in print @Int (f 1 + g 2)
