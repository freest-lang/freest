module InInPat where

f : ?(?Int ; Wait) ; Wait -> ()
f (?(?1    ; Wait) ; Wait) = print 1
f (?(?2    ; Wait) ; Wait) = print 2
f (?(?x    ; Wait) ; Wait) = print x

main =
  let (inr,   inw)   = channel @(?Int ; Wait)
      (ininr, ininw) = channel @(?(?Int ; Wait) ; Wait)
  in fork (\(_ : ()) -1-> 
       ininw |> send inr |> close ;
       inw |> send 3 |> close);
     f ininr