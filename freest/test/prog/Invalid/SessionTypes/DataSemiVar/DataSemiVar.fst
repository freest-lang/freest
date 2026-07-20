data Tree = Leaf

marshall : forall a -> Tree ; a -> ()
marshall Leaf = ()
