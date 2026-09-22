-- `*?p` abbreviates `*?p; q` when the continuation is not needed.

get : *?Int -> Int
get (*?x) = x

main : ()
main =
  let (w, r) = channel @(*!Int) in
  send_ 42 w;
  print (get r)
