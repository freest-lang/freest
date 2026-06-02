module MConsumedInUnFun where

foo : forall #m #n (a : m T) -> a -> (a -> ()) -> ()
foo #m #n @a x f = f x