-- The unpacked existential's witness type would escape its scope through a
-- channel whose element type is still open, and be received as a Char.
type P = (exists (c : *T), (c, c -> Int))

mk : Int -> P
mk n = (@Int, (n, \i -> i)) : P

initQueue : forall a -> () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)

main : ()
main =
  let (r, w) = initQueue () in
  let (@d, (v, g)) = mk 4 in
  let _ = send_ v w in
  print @Char (receive_ r)
