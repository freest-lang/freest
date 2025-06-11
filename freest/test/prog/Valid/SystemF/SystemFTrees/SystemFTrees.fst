{- |
Module      : SystemFTrees
Description : Binary trees with leaves of type A
Copyright   : (c) Vasco T. Vasconcelos

Church Encoding _ Binary trees with leaves of type A

Jean-Yves Girard
The Blind Spot
European Mathematical Society, 2011
-}

module SystemFTrees where

type Tree : *T -> *T
type Tree a = forall (t : *T) . a -> (t -> t -> t) -> t

main : Int
main = 5

-- TO BE CONTINUED
