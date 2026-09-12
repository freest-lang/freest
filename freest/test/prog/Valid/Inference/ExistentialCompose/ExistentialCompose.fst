{- Existential *composition*: unpack an abstract type, then re-pack it into
   another existential, with `Box`'s binder kind left to inference.

   `rebox` is never used, which is what makes `Box`'s binder unrestricted: the
   usage rules bound a type name by how it is used, so the unused definition
   forces `*` on the binder rather than leaving it at the top. -}
type Box = (exists a, (a, a -> Int))

box : Box
box = (@Int, (7, \i -> i)) : Box

rebox : Box
rebox = (@c, (x, f)) : Box
  where (@c, (x, f)) = box
