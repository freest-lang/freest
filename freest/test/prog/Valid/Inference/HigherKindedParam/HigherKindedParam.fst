module HigherKindedParam where

-- A higher-kinded parameter `f` is applied in a field (`f a`); its arrow kind is
-- inferred from that use, so the datatype kinds without an annotation. Recursive
-- (`Fix`) and type-level application (`App Box Int`) work too. (Constructing a
-- value still needs type-application inference for `f`, a separate type-inference
-- limitation — not exercised here.)
data Box a   = MkBox a
data App f a = MkApp (f a)
data Fix f   = In (f (Fix f))

unApp : App Box Int -> Int
unApp x = case x of MkApp b -> (case b of MkBox n -> n)

main : ()
main = print 0
