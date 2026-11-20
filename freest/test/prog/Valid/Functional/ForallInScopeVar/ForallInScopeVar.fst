-- A local signature with a forall of its own may still mention a type variable
-- already in scope: forall-or-nothing concerns only the variables that are not.
f : forall a -> a -> a
f @a x = go @Int x 0
  where
    go : forall b -> a -> b -> a
    go @b y _ = y

main : ()
main = print (f @Int 5)
