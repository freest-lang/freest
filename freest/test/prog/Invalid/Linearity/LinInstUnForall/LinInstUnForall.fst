module LinInstUnForall where

f : forall (a : *T) -> a -> a
f @a x = x

g : (?Int; Close) -> (?Int; Close)
g = f
