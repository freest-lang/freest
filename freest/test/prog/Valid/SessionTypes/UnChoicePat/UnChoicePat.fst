-- The continuation of `*&l p` is the same unrestricted channel, so successive
-- choices can be matched by one pattern.

type C : *C
type C = *&{L, M}

twice : C -> Int
twice (*&L (*&L _)) = 1
twice (*&L (*&M _)) = 2
twice (*&M (*&L _)) = 3
twice (*&M (*&M _)) = 4

main : ()
main =
  let (w, r) = channel @(*+{L, M}) in
  select_ L w; select_ M w;
  print (twice r)
