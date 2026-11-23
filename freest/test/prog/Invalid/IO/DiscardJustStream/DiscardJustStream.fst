-- The stream inside `Just'` is linear: matching it with a wildcard discards
-- it without closing it.

main : ()
main = case openReadFile "test/prog/Valid/IO/OpenReadFile/lines.txt" of
  Just' _  -> ()
  Nothing' -> ()
