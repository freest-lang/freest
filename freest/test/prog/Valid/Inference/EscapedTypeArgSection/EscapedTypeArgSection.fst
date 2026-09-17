-- A section leaves its operator's result type open; the use binds it.
main : ()
main = let g = (5 |>) in print @Int (g (\(x:Int) -> x + 1))
