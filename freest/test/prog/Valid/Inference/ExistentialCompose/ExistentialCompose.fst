{- Existential *composition*: unpack an abstract type, then re-pack it into
   another existential. The unpacked `c`'s real kind is a typing fact learned
   from the unpack; at the re-pack, kinding sees only its placeholder (defaulted
   to the top `1T`) and rejects it against `Box`'s `*T` binder. Passes today only
   with the annotation `(c : *T)` on the unpack. -}
module ExistentialCompose where

type Box = (exists a, (a, a -> Int))

box : Box
box = (@Int, (7, \i -> i)) : Box

rebox : Box
rebox = (@c, (x, f)) : Box
  where (@c, (x, f)) = box
