-- `a`'s kind is written nowhere, so nothing settles it before the call: `g`'s
-- instantiation at `UnId` is what says it must be `*T`. Instantiating it at a
-- linear arrow and then using `f` twice must be rejected, and it is rejected
-- whichever kind is written for `a` -- `*T` by a kind mismatch, `1T` by the
-- multiplicity clash below -- so inference must reject it too.
--
-- The witness is for the call bound: it is emitted by pairing the argument's
-- kind with the binder's structurally, over a catch-all that emits nothing, so
-- a binder kind left as a whole-kind variable makes the check go quiet rather
-- than fail. Written on purpose -- no suite covers it.
type UnId (a : *T) = a

pass : forall g a -> g a -> g a
pass x = x

main : ()
main = let f = pass @UnId @(Int -1-> Int) (\(x:Int) -1-> x) in print @Int (f 1 + f 2)
