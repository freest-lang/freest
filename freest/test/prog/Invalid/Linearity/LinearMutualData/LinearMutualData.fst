module LinearMutualData where

-- `A` holds a linear field (a channel), so the mutual-recursion multiplicity
-- solve must infer `A : 1T`; discarding `a` is then a linearity error. (If the
-- multiplicity solver regressed and inferred `*T`, this would wrongly compile.)
data A = MkA (!Int ; Close) B
data B = MkB A

f : A -> ()
f a = ()

main : ()
main = ()
