module MutualRecData where

data RedBlackTree = Node Colored | Empty

data Colored = Red RedBlackTree Int RedBlackTree
             | Black RedBlackTree Int RedBlackTree

main : ()
main = print (Node (Red (Node (Red Empty 
                                   1 
                                   (Node (Black Empty
                                                3
                                                Empty))))
                   5
                   (Node (Black Empty 
                                7
                                Empty))))
