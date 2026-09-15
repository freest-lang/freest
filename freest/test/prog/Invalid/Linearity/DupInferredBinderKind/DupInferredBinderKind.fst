-- The body duplicates x, so a's inferred kind must be unrestricted; the call's
-- check against it is solved locally and forgotten, duplicating a linear value.
dup : forall a -> a -> (a, a)
dup x = (x, x)

main : ()
main = let (f, g) = dup (\(x:Int) -1-> x) in print @Int (f 1 + g 2)
