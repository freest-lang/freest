{- A value-level type abstraction `\@c ...` with an omitted binder kind takes
   its kind from the forall it is checked against (here `*T` from `Poly`),
   rather than requiring `\@(c:*T)`. -}
module TypeLambdaInferKind where

type Poly : *T
type Poly = forall (c : *T) -> c -> c

idp : Poly
idp = \@c x -> x

main : ()
main = print (idp @Int 5)
