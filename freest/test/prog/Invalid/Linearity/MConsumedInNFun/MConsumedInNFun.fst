module MConsumedInNFun where

foo : forall #m #n (a : m T) -> a -> (a -> ()) -n-> ()
foo #m #n @a x f = f x