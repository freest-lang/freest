{- Regression: a datatype with an omitted parameter kind, applied to a type
   variable (polymorphic use, e.g. `Box a`), must terminate. It produces a
   cyclic multiplicity binding, and the ACUI solver's `apply` had no cycle
   guard, so kind inference looped, allocating unboundedly. -}
module PolyDataParamKind where

data Box a = MkBox a
type U a = Box a

unwrap : forall a -> Box a -> a
unwrap @a b = case b of MkBox x -> x

main : ()
main = print (unwrap @Int (MkBox 42))
