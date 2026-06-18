module WaitAndVarCase where

f : Wait -> ()
f c = case c of
  Wait -> ()
  c'   -> wait c'
