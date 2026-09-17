-- Each guarded result is instantiated where the tuple pattern matches it.
pairOf : forall a -> (Maybe a, Int)
pairOf @a = (Nothing, 3)

other : forall a -> (Maybe a, Int)
other @a = (Nothing, 4)

pick : Bool -> Int
pick b = n
  where (m, n) | b = pairOf
               | otherwise = other

main : ()
main = print @Int (pick False)
