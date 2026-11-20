type T : 1C
type T = Wait

main : ()
main = let (r,w) = channel @T in fork (\_ -1-> close w); wait r
