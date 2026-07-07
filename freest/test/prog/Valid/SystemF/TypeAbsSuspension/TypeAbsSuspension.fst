g : Int -> forall a -> Int
g x @a = g x @a

h : (forall a -> Int) -> Int
h _ = 0

main : ()
main = print (h (g 5))
