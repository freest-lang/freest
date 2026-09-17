-- const 5 leaves its second type argument open; both uses agree on it.
main : ()
main = let k = const 5 in print @Int (k True + k False)
