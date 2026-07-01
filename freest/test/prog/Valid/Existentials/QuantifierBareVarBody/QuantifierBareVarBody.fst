{- Regression: a quantifier whose body is exactly the bound (kind-omitted)
   variable must kind-check, not crash. With an omitted binder the body
   variable's kind is an unsolved kind variable; the AppQuant/AppQuantS smart
   constructors eagerly match `Proper _ _ _` on the body's kind, which used to
   throw a non-exhaustive-patterns error for `exists a, a`, `!type a. a` and
   `?type a. a` (`forall a -> a` escaped only by laziness). Fixed in
   `checkOperand` by carrying the instantiated proper kind on the body. -}
module QuantifierBareVarBody where

type ExistsVar = (exists a, a)
type ForallVar = (forall a -> a)
type SendTypeVar = (!type a . a)
type RecvTypeVar = (?type a . a)

main : ()
main = print 0
