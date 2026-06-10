module InInAndVar where

f : ?(?Int ; Wait) ; Wait -> ()
f (?(?1    ; Wait) ; Wait) = print 1
f (?(?2    ; Wait) ; Wait) = print 2
f (?x ; Wait) = x |> receive |> snd |> wait