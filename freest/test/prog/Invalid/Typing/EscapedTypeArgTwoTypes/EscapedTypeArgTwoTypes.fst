-- The open type argument of const 5 is bound once; a second use at another type is a mismatch.
main : ()
main = let k = const 5 in print @Int (k True + k 'c')
