module InInAndVarCase where

f : ?(?Int ; Wait) ; Wait -> ()
f c = case c of
  ?(?1 ; Wait) ; Wait -> print 1
  ?(?2 ; Wait) ; Wait -> print 2
  c' -> case c' of
          ?x ; Wait -> x |> receive |> snd |> wait
