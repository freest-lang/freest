module VarAndInCase where

f : ?Int -> Skip
f c = case c of
  ?_ ; c' -> c'
  c'      -> snd (receive c')
