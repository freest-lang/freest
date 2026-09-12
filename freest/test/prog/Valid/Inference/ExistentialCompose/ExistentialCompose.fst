{- Existential *composition*: unpack an abstract type, then re-pack it into
   another existential, with `Box`'s binder kind left to inference.

   `rebox` is consumed below because nothing else would justify `Box`'s binder
   being unrestricted: it is a type declaration, and the usage rules only bound
   a bare type variable, so an unused `rebox` makes `Box` linear and the
   definition unconsumed. Bounding a type name by its usage is the general fix;
   see `local-multiplicity-free-choices.md`. -}
type Box = (exists a, (a, a -> Int))

box : Box
box = (@Int, (7, \i -> i)) : Box

rebox : Box
rebox = (@c, (x, f)) : Box
  where (@c, (x, f)) = box

_ = let (@c, (x, f)) = rebox in f x
