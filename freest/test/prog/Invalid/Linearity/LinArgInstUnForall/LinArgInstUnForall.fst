module LinArgInstUnForall where

-- The argument-driven mirror of LinInstUnForall. A linear closure is passed where
-- 'f's '*T'-bound (unrestricted) type variable is inferred, forcing an
-- unsatisfiable '1 <= *'. Because the argument is not a variable or application,
-- it drives the quickLook instantiation-variable linking rather than match's.

f : forall (a : *T) -> a -> a
f @a x = x

g : () -1-> ()
g = f (\(x:()) -1-> x)
