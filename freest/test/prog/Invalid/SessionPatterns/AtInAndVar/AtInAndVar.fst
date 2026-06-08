module AtInAndVar where

f : *?Int -> *?Int
f c@(?1 ; _) = c
f c = c
