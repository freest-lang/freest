{-
Existential *composition*: unpack an abstract type, then re-pack it into
another existential. The unpacked `c`'s real kind is a typing fact learned
from the unpack; at the re-pack, kinding sees only its placeholder (defaulted
to the top `1T`) and rejects it against `Box`'s `*T` binder. Passes today only
with the annotation `(c : *T)` on the unpack.
-}

type Box = (exists a, (a, a -> Int))

box : Box
box = (@Int, (7, \i -> i)) : Box

rebox : Box
rebox = (@c, (x, f)) : Box
  where (@c, (x, f)) = box

{-
Existential composition (item 2, type-level face).

Awaiting: kinding that consults the scrutinee's existential type so an unpacked
abstract type is bound at the existential's own binder kind, rather than a
phase-B placeholder that leaks (defaulted to 1T) when the type is re-packed.
Once solved expect empty output.
-}