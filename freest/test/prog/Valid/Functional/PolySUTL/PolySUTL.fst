id' : forall a -> a -> a
id' @a x = x

f : Int -1-> Int
f x = 2 * x

main : ()
main =
  print ((id' @(Int -1-> Int) f) 5)
