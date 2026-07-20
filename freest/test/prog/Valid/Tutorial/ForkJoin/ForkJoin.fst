-- _ =
--     let ()
--     fork (\_ -> putChar 'A') ;
--     fork (\_ -> putChar 'B') ;
--     fork (\_ -> putChar 'C') ;
--     ()

_ =
    let (w, r) = channel @ForkJoin in
    fork (\_ -> putChar 'A'; join w) ;
    fork (\_ -> putChar 'B'; join w) ;
    fork (\_ -> putChar 'C'; join w) ;
    await 3 r