-- Ends with 'close' in a buffer: the main thread closes and terminates
-- before the forked thread waits. The fixed version, in
-- Valid/SessionTypes/TypeDefEnd, forks the closing side instead.

type T : 1C
type T = Wait

main : ()
main = let (r,w) = channel @T in fork (\_ -1-> wait r); close w
