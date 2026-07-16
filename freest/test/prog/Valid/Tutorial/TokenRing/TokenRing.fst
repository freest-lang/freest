type Forward = &{Done: Wait, More: Forward}

relay : Forward -> Dual Forward -1-> ()
relay (&Done Wait) d = d |> select Done |> close
relay (&More c)    d = d |> select More |> relay c

-- The distinguished/asymmetric machine in a token ring
root : Int -> Forward -> Dual Forward -1-> ()
root 0 c d =
    let d = d |> select Done |> close
    in case c of (&Done Wait) -> ()
root n c d = 
    let d = select More d
    in case c of (&More c) -> print n ; root (n - 1) c d

ring : ()
ring =
    let (c1, d1) = channel @Forward
        (c2, d2) = channel @Forward
        (c3, d3) = channel @Forward
    in fork (\_ -1-> relay c1 d2) ;  -- ch1 → ch2
       fork (\_ -1-> relay c2 d3) ;  -- ch2 → ch3
       root 10 c3 d1                 -- ch3 → ch1 (closes the ring 1→2→3→1)
