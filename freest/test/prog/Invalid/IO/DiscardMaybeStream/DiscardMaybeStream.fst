-- A `Maybe'` is linear: the result of opening a file cannot be discarded,
-- since it may hold a stream that must be closed.

main : ()
main =
  let _ = openReadFile "test/prog/Valid/IO/OpenReadFile/lines.txt" in
  ()
