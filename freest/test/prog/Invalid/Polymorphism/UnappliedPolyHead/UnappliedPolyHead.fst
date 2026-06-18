module UnappliedPolyHead where

type List : *T -> *T
type List a = forall (r : *T) -> (a -> r -> r) -> r -> r

nil : forall (a : *T) -> List a
nil @a @r c n = n

empty : List Char
empty = nil
