-- _ =
--     let ()
--     fork (\_ -> print 'A') ;
--     fork (\_ -> print 'B') ;
--     fork (\_ -> print 'B') ;
--     ()

_ =
    let (w, r) = channel @ForkJoin in
    fork (\_ -> putChar 'A'; join w) ;
    fork (\_ -> putChar 'B'; join w) ;
    fork (\_ -> putChar 'C'; join w) ;
    await 3 r