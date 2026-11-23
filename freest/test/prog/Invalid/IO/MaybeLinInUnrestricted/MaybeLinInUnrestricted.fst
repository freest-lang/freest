-- `Maybe'` has kind `1T -> 1T`: it cannot be used where an unrestricted type
-- is expected.

f : Maybe' Int -> Maybe' Int
f m = m

main : ()
main = print @(Maybe' Int) (f Nothing')
