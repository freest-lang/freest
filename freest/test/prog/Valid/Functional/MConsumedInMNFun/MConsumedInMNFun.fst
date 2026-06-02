module MConsumedInMNFun where

foo : forall #m #n (a : m T) -> a -> (a -> ()) -m+n-> ()
foo #m #n @a x f = f x