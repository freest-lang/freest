-- Forcing undefined is a runtime exception at the undefined, not a compiler error.
main : ()
main = print @Int (undefined @Int + 1)
