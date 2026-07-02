{- A list whose element is a type variable with an omitted kind: the element
   position must instantiate the variable's kind (as tuples and arrows do),
   rather than requiring it to be proper already. `forall a -> [a] -> [a]`
   used to report "could not infer a proper kind for a". -}
module ListPolyInferKind where

g : forall a -> [a] -> [a]
g @a x = x

main : ()
main = print (g @Int ([1, 2, 3] @Int))
