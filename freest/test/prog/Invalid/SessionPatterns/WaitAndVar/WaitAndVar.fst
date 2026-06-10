module WaitAndVar where

f : Wait -> ()
f Wait = ()
f c = wait c