-- g is applied to its own result. Its parameter multiplicity is inferred to
-- the least solution, which is what lets `@UnId` (parameter `*T`) instantiate
-- it: the top would fix it linear and reject.
type UnId (a : *T) = a

pass : forall g -> g (g Int) -> g (g Int)
pass x = x

main : ()
main = print @Int (pass @UnId 3)
