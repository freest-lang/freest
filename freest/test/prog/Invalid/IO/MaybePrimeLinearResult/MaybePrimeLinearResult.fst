-- `maybe'` discards either the default value or the function, so its result
-- type must be unrestricted: it cannot produce a stream.

main : ()
main =
  let out = maybe' @OutStream @OutStream
              (openWriteFile "/tmp/freest-test-invalid-maybe-prime.txt")
              (\o -> o)
              (openWriteFile "/tmp/freest-test-invalid-maybe-prime.txt") in
  hCloseOut out
