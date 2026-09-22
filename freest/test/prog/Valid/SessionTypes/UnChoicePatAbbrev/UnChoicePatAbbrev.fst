-- `*&l` abbreviates `*&l p` when the continuation is not needed.

type C : *C
type C = *&{L, M}

pick : C -> Int
pick (*&L) = 1
pick (*&M) = 2

main : ()
main =
  let (w, r) = channel @(*+{L, M}) in
  select_ M w;
  print (pick r)
