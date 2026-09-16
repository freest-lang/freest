-- f1's binder is bounded by #m in its body and by f0 through a call; g's
-- binder, bounded through f1, must see both.
f0 : forall a0 -> a0 -> (a0, a0)
f0 x = (x, x)

f1 : forall #m a1 -> a1 -> (a1 -> ()) -m-> (a1, a1)
f1 #m @a1 x k = f0 x

g : forall #n c -> c -> (c -> ()) -n-> (c, c)
g #n @c y k = f1 #n y k

sink : Int -> ()
sink _ = ()

main : ()
main = let (u, v) = g #* 1 sink in print @Int (u + v)
