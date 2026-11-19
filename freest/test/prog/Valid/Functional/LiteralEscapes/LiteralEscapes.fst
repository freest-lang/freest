main : ()
main =
  print ['\t', '\'', '\\', '"', '\65', '\x41', '\o101', '\^A', '\SOH'];
  print "\SO\&H";
  putStrLn "quote \", tick ', gap \
           \continued";
  putStrLn ("a\\" ++ "b")
