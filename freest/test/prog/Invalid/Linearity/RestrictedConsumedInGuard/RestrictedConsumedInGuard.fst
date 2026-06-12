module RestrictedConsumedInGuard where

f : forall #m (a : m T) -> (a -> Bool) -> a -> Int
f #m @a g x | g x = 1
