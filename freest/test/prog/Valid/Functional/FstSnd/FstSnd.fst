fst' : forall a b -> (a, b) -> a
fst' @a @b p = let (x, _) = p in x

snd' : forall a b -> (a, b) -> b
snd' @a @b p = let (_, y) = p in y

main : ()
main = print (fst' (5, 'h') + snd' (True, 7))
