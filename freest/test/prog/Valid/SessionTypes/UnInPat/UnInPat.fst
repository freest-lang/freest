-- The continuation of `*?p; q` is the same unrestricted channel, so several
-- inputs can be matched by one pattern.

firstOf : *?Int -> Int
firstOf (*?x ; _) = x

sumOfTwo : *?Int -> Int
sumOfTwo (*?x ; *?y ; _) = x + y

main : ()
main =
  let (w, r) = channel @(*!Int) in
  send_ 3 w; send_ 4 w;
  print (sumOfTwo r);
  send_ 5 w;
  print (firstOf r)
