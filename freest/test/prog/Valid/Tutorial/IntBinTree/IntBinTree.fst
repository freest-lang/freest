data IntBinaryTree = Leaf | Node IntBinaryTree Int IntBinaryTree

treeSum : IntBinaryTree -> Int
treeSum Leaf = 0
treeSum (Node l x r) = treeSum l + x + treeSum r

aTree : IntBinaryTree
aTree = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)

_ = print (treeSum aTree)