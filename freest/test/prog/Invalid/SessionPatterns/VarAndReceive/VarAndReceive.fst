module VarAndReceive where

f : ?Int -> Skip
f c = snd (receive c)
f (?_ ; c) = c