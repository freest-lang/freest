module AtChoiceAndVar where

f : *&{L} -> *&{L}
f c@(&L _) = c
f c = c
