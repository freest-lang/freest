f : !Int -> ()
f c = if True then () else send 5 c; ()
