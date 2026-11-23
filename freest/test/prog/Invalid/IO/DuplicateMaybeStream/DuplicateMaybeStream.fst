-- A `Maybe'` is linear: the result of opening a file cannot be used twice.

closeIn : Maybe' InStream -> ()
closeIn (Just' c) = hCloseIn c
closeIn Nothing'  = ()

main : ()
main =
  let m = openReadFile "test/prog/Valid/IO/OpenReadFile/lines.txt" in
  closeIn m;
  closeIn m
