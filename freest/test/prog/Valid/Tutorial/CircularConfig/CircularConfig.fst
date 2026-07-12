type Forward = &{Done: Wait, More: Forward}

-- sink' : Forward -> ()
-- sink' (&Done Wait) = ()
-- sink' (&More c)    = print "More" ; sink' c

forward : Forward -> Dual Forward -1-> ()
forward (&Done Wait) d = d |> select Done |> close
forward (&More c)    d = d |> select More |> forward c

master : Int -> Forward -> Dual Forward -1-> ()
master 0 c d =
    let d = d |> select Done |> close
    in case c of (&Done Wait) -> ()
master n c d = 
    let d = select More d
    in case c of (&More c) -> print n ; master (n - 1) c d
-- master 0 c d = d |> select Done |> close ; sink' c
-- master n c d = print n ; master (n - 1) c (select More d)

circle : ()
circle =
    let (c1, d1) = channel @Forward
        (c2, d2) = channel @Forward
        (c3, d3) = channel @Forward
    in fork (\_ -1-> forward c2 d2) ;
       fork (\_ -1-> forward c1 d3) ;
       master 10 c3 d1

-- _ = print $ fork #* @Int (\_ -> 5)
